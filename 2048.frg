#lang forge "dining_smiths/polite_smiths" "<anonymous email>"

option problem_type temporal
option max_tracelength 5
option min_tracelength 5
// option solver Glucose

/**
* Overarching signature representing the board. 
*/
one sig Board {
    // Map of location of squares. 
    squares : pfunc Int -> Int -> Square
}

/**
 * Abstract sig representing directions (ie right, left, etc) on the 
 * board. 
*/
abstract sig Direction {
    // Corresponding map of one square to another. 
    ord: pfunc Square -> Square
}

/**
 * Implementations of the direction sig for the four directions one can
 * swipe.
*/
one sig Right extends Direction {}
one sig Left extends Direction  {}
one sig Up extends Direction    {}
one sig Down extends Direction  {}

/** 
 * Squares represent individual squares on the board, with a variable "cell"
 * of which cell they are holding to at a given time. 
*/
sig Square {
    var cell: lone Cell // May or may not be filled
}

/**
 * These are the fundamental block objects that show up on screen and slide around.
 * Cells keep track of their parents (who merged into them) and children (who they 
 * merge into)
*/
sig Cell { 
    value : one Int, // Values constant during cell's lifetime

    child: lone Cell, // Results of merging
    parents: set Cell, // What (if any) the block merged from. 

    var location: lone Square // Inverse of cell map
}

/**
 * The board is a grid of the desired size. 
 */ 
pred fourByFour[size: Int] {
    // Domain of squares map is 4x4 grid
    Board.squares.Square = {r: Int, c: Int | {
        0 <= r and r < size
        0 <= c and c < size
    }}

     // Surjectivity
    Square = Board.squares[Int][Int]
     // Injectivity
    all r1, r2, c1, c2: Int {
        {
            some Board.squares[r1][c1] 
            some Board.squares[r2][c2]
            r1 != r2 or c1 != c2
        } => {
            Board.squares[r1][c1] != Board.squares[r2][c2]
        }
    }
}

/**
 * Potential optimizer for the board.
 */ 
// inst optimizer {
    // we probably don't need these since we have a lot more than 2 board states 
//     -- 2 board states
//     PuzzleState = `PuzzleState0
//     SolvedState = `SolvedState0
    // but this could be helpful
//     BoardState = PuzzleState + SolvedState
//     -- Upper-bound on the board relation: don't even try to use
//     -- a row, column, or value that's outside the interval [1, 9]
//     board in BoardState -> 
//              (1 + 2 + 3 + 4) -> 
//              (1 + 2 + 3 + 4) -> 
//              (1 + 2 + 3 + 4)

//     -- encode the set of values in bounds, not constraints
//     Helper = `Helper0
//     values = Helper -> (1 + 2 + 3 + 4)
// }

/**
 * Checks that the grid of size `size` has properly aligned direction orderings
 * for up, down, left, and right. 
*/
pred ordered[size: Int] {
    all r : Int | all c : Int {
        {0 <= r and r < size and 0 <= c and c < size} => {
            // Set to corresponding location. Notably, don't need to 
            // check edge cases, as will evaluate to None anyway.
            // Using succ relation because integer addition was giving
            // problems
            (Board.squares[c][r]).(Down.ord)  = Board.squares[c][r.succ]
            (Board.squares[c][r]).(Up.ord)    = Board.squares[c][succ.r]
            (Board.squares[c][r]).(Right.ord) = Board.squares[c.succ][r]
            (Board.squares[c][r]).(Left.ord)  = Board.squares[succ.c][r]
        }
    }
}

/**
 * General well-formedness of parenthood conditions. 
*/
pred parenthoodWellFormed {
    // No self-parenthood
    no iden & parents
    // Child is inverse of parents
    child = ~parents

    all c: Cell {
        // Either 2 parent or no parents
        #{c.parents} = 0 or #{c.parents} = 2

        // Parent's value is one less than child's 
        some c.parents => {
            c.parents.value.succ = c.value
        }
    }
}

/**
 General well-formedness conditions of the relationship between squares and cells.
*/
pred cellWellFormed {
    // .cell is injective where it exists
    always {all disj s1, s2: Square {
        s1.cell != s2.cell or no s1.cell or no s2.cell
    }}

    // location is inverse as expected
    always cell = ~location

    // Value positive
    cell.value > 0
}

/**
 * There is a valid starting board.
 * All of the boxes are empty save for two (which have the lowest 
 * denominations -- the same that appear on a turn)
 */
pred init {
    // Exactly 2 starting cells
	#{Square.cell} = 2

    // Starting cells either 1 or 2 (eg. 2 or 4)
	Square.cell.value in {i: Int | i = 1 or i = 2}
}

/**
 * Guarantees the board is nonempty. Useful for generating counterexamples.
 */
pred nonEmpty {
    always some Square.cell
}

/**
* Guard for whether player can slide blocks in given direction. 
*/
pred guard[dir: Direction] {
    some s: Square | {
        some s.(dir.ord)
        some s.cell
        s.(dir.ord).cell = none or s.(dir.ord).cell.value = s.cell.value
    }
}

/**
 * This guarantees that the cells on the board are all either merged or
 * stay on the board, with child nodes appearing appropriately for merging.
 * All of this is with the exception of the `added` cell, which is the one that
 * has just shown up on screen. 
*/
pred mergeOrMaintain[added: Cell] {
    // All cells in the board keep either themselves or a child in the 
    // new board, but not both
    all c: Square.cell | {
        no c.child => {
            c in Square.cell'
        } else {
            c in Square.cell' or c.child in Square.cell'
            not {c in Square.cell' and c.child in Square.cell'}
        }
    }

    // New cell is new on board.
    added in Square.cell' - Square.cell
    no added.parents // New is not parent of anything
    added.value = 1 or added.value = 2 // Value either 1 or 2

    // All cells in the new board had either themselves or both parents in 
    // the previous board
    all c: Square.cell' - added | {
        {not c in Square.cell} <=> {
            # {c.parents & Square.cell} = 2
        }
    }
}

/**
 * Guarantees that cells remain on the same row/col in the next state (or their 
 * children do). 
*/
pred rowColPreserved[dir: Direction] {
    all c: Square.cell {
        // Location on the same row
        c in Square.cell' => {
            c.location -> c.location' in ^(dir.ord + ~(dir.ord) + iden)
        }
        // OR location of child in the same row
        c.child in Square.cell' => {
            c.location -> c.child.location' in ^(dir.ord + ~(dir.ord) + iden)
        }
    }
}

/**
 * Makes sure that if two cells are next to each other in the designated 
 * direction and have the same value, that at least the second one will
 * be merged in the following state. 
*/
pred forceMerge[dir: Direction] {
    // This represents right adjacentcy modulo empty spaces in between. 
    let cellDir = {c1: Cell, c2: Cell | {
        c1 in Square.cell
        c2 in Square.cell
        c1.location -> c2.location in ^(dir.ord)
        no c3 : Square.cell {
            c1.location -> c3.location in ^(dir.ord)
            c3.location -> c2.location in ^(dir.ord)
        }
    }} | {
    all c : Square.cell {
        c.cellDir.value = c.value => {
            c.cellDir not in Square.cell'
        }
    }}
}

/**
 * Checks that the cells in a state are "up against" the wall in a given direction, with no
 * free spaces in between. Exception for new cell after transition. 
*/
pred pushed[dir: Direction, added: Cell] {
    all s: Square {
        some s.cell - added => {
            no s.(dir.ord) or some (s.(dir.ord).cell - added)
        }
    }
}

/**
 * Full transition predicate for swiping the cells in a given direction. Uses a combination of 
 * the previous helper predicates, along with a check that the order of cells has not changed
 * (up to replacement of certain cells with their children).
*/ 
pred swipe[dir:Direction, added: Cell] {
    guard[dir]
    forceMerge[dir]
    next_state pushed[dir, added]
    mergeOrMaintain[added]
    rowColPreserved[dir]

    // This is the ordering of cells that shows up in the final state, other than newly added cell.
    let finalOrdering = {c1: Cell, c2: Cell | {
        c1 in Square.cell' - added
        c2 in Square.cell' - added
        c1.location' -> c2.location' in dir.ord
    }} | {

        all c1: Cell, c2: Cell {{
            // This first part allows us to check over all cells that are next to each other in the
            // given direction *modulo* cells in between. In other words if we have C1 -> Empty -> C2
            // -> C3, the ordering would be C1 -> C2 -> C3. 
            c1 in Square.cell
            c2 in Square.cell
            c1.location -> c2.location in ^(dir.ord)
            no c3 : Square.cell {
                c1.location -> c3.location in ^(dir.ord)
                c3.location -> c2.location in ^(dir.ord)
            }
        } => {
            // Checks that for each of these paired orderings, same pair shows up in the final order,
            // up to replacement with children.
            {
                c1 -> c2 in finalOrdering
            } or {
                some c1.child
                c1.child -> c2 in finalOrdering
            } or {
                some c2.child
                c1 -> c2.child in finalOrdering
            } or {
                some c1.child and some c2.child
                c1.child -> c2.child in finalOrdering
            } or {
                some c1.child
                c1.child = c2.child
            }
        }
    }}
}

// Predicate to allow for doing nothing
pred doNothing {
    cell = cell'
    location = location'
}

pred wellFormed[size: Int] {
    fourByFour[size]
    ordered[size]
    cellWellFormed
    parenthoodWellFormed
}

/**
    Traces predicate. Takes all well-formedness conditions, along with initilization,
    and checks that the state remains constant. 
*/ 
pred traces[size: Int] {
    wellFormed[size]
    init
    always {
        doNothing or {some dir : Direction | one added: Cell | swipe[dir, added]}
    }
    always {doNothing => always doNothing}
}

run {
    traces[4]
    eventually {4 in Square.cell.value}
} for exactly 16 Square, 10 Cell