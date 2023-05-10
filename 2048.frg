#lang forge "dining_smiths/polite_smiths" "<anonymous email>"

option problem_type temporal
option max_tracelength 5
option min_tracelength 5
option solver Glucose

one sig Board {
    squares : pfunc Int -> Int -> Square
}

abstract sig Direction {
    ord: pfunc Square -> Square
}

one sig Right extends Direction {}
one sig Left extends Direction  {}
one sig Up extends Direction    {}
one sig Down extends Direction  {}

/** 
 * Instead of Board referring directly to the cells, it might
 * be helpful to abstract away another layer of "squares", which
 * can store some extra positioning information. Could also be removed.
*/
sig Square {
    var cell: lone Cell // May or may not be filled
}

sig Cell { // Maybe rename to block?
    value : one Int, // Values constant during cell's lifetime

    child: lone Cell, // Results of merging
    parents: set Cell,

    var location: lone Square 
}

/**
 * The board is a four-by-four grid
 * Well formed-ness 
 */ 
pred fourByFour[size: Int] {
    // Domain of squares map is 4x4 grid
    Board.squares.Square = {r: Int, c: Int | {
        0 <= r and r < size
        0 <= c and c < size
    }}

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
 * Guarantees that the square's "left", "right", etc position
 * values are set correctly. 
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

        // Parents are 
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
}

/**
 * There is a valid board.
 * All of the boxes are empty save for two (which have the lowest 
 * denomination -- the same that appear on a turn)
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
* Guard for whether player can slide blocks to right. Can if there
* is a cell with same numbered to its right or empty cell.
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
 * Guarantees that cells remain on the same row in the next state (or their 
 * children do). For use in either the right or left transition predicates.
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
 * Makes sure that, if two cells are next two each other with the same value,
 * and either left or right is swiped, the two will merge together. 
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
 * Checks that the cells in a state are "up agains" the right wall, with no
 * free spaces to the right of cells. 
*/
pred pushed[dir: Direction, added: Cell] {
    all s: Square {
        some s.cell - added => {
            no s.(dir.ord) or some (s.(dir.ord).cell - added)
        }
    }
}

// See above
pred swipe[dir:Direction, added: Cell] {
    guard[dir]
    forceMerge[dir]
    next_state pushed[dir, added]
    mergeOrMaintain[added]
    rowColPreserved[dir]

    let finalOrdering = {c1: Cell, c2: Cell | {
        c1 in Square.cell' - added
        c2 in Square.cell' - added
        c1.location' -> c2.location' in dir.ord
    }} | {
        all c1: Cell, c2: Cell {{
            c1 in Square.cell
            c2 in Square.cell
            c1.location -> c2.location in ^(dir.ord)
            no c3 : Square.cell {
                c1.location -> c3.location in ^(dir.ord)
                c3.location -> c2.location in ^(dir.ord)
            }
        } => {
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

/**
    Traces predicate. Takes all well-formedness conditions, along with initilization,
    and checks that the state remains constant. 
*/ 
pred traces[size: Int] {
    fourByFour[size]
    ordered[size]
    cellWellFormed
    parenthoodWellFormed
    init
    always {
        doNothing or {some dir : Direction | one added: Cell | swipe[dir, added]}
    }
    always {doNothing => always doNothing}
}

run {
    traces[2]
    eventually {4 in Square.cell.value}
} for exactly 4 Square, 10 Cell