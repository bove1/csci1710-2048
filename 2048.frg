#lang forge "dining_smiths/polite_smiths" "<anonymous email>"

option problem_type temporal
option max_tracelength 8
option min_tracelength 3
option solver Glucose

one sig Board {
    squares : pfunc Int -> Int -> Square
}

/** 
 * Instead of Board referring directly to the cells, it might
 * be helpful to abstract away another layer of "squares", which
 * can store some extra positioning information. Could also be removed.
*/
sig Square {
    var cell: lone Cell, // May or may not be filled

    // Might be helpful to keep track of what's in each direction?
    up:    lone Square,
    down:  lone Square,
    left:  lone Square,
    right: lone Square
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
pred fourByFour {
    // Domain of squares map is 4x4 grid
    Board.squares.Square = {r: Int, c: Int | {
        0 <= r and r < 3
        0 <= c and c < 3
    }}

    Square = Board.squares[Int][Int]
     // Easier to hard-code this then injectivity since we're already
     // Hardcoding the 4x4 size
    # Board.squares = 9
}

/**
 * Guarantees that the square's "left", "right", etc position
 * values are set correctly. 
*/
pred ordered {
    all r : Int | all c : Int {
        {0 <= r and r < 3 and 0 <= c and c < 3} => {
            // Set to corresponding location. Notably, don't need to 
            // check edge cases, as will evaluate to None anyway.
            // Using succ relation because integer addition was giving
            // problems
            (Board.squares[c][r]).down  = Board.squares[c][r.succ]
            (Board.squares[c][r]).up    = Board.squares[c][succ.r]
            (Board.squares[c][r]).right = Board.squares[c.succ][r]
            (Board.squares[c][r]).left  = Board.squares[succ.c][r]
        }
    }
}

/**
 * General well-formedness of parenthood conditions. 
*/
pred parenthoodWellFormed {
    // No self-parenthood
    no iden & parents

    all c: Cell {
        // Either 2 parent or no parents
        #{c.parents} = 0 or #{c.parents} = 2
        child = ~parents

        // Parent/child inverse property
        some c.child => {
            c.child.value = c.value.succ
        }

        // Other direction
        some c.parents => {
            c.parents.value = succ.(c.value)
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
    all c: Cell {
        always {c in Square.cell => {
            c.location.cell = c
        } else {
            no c.location
        }}

        always not {
            c in Square.cell
            some c.child
            c.child in Square.cell
            }
    }
}

/**
 * There is a valid board.
 * All of the boxes are empty save for two (which have the lowest 
 * denomination -- the same that appear on a turn)
 */
pred init {
    // Exactly 2 starting cells
	#{Square.cell} = 4

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
pred guardRight {
    some s: Square | {
        some s.right
        some s.cell
        s.right.cell = none or s.right.cell.value = s.cell.value
    }
}

/**
* Guard for whether player can slide blocks to right. Can if there
* is a cell with same numbered to its right or empty cell.
*/
pred guardLeft {
    some s: Square | {
        some s.left
        some s.cell
        s.left.cell = none or s.left.cell.value = s.cell.value
    }
}

/**
* Guard for whether player can slide blocks to right. Can if there
* is a cell with same numbered to its right or empty cell.
*/
pred guardUp {
    some s: Square | {
        some s.up
        some s.cell
        s.up.cell = none or s.up.cell.value = s.cell.value
    }
}

/**
* Guard for whether player can slide blocks to right. Can if there
* is a cell with same numbered to its right or empty cell.
*/
pred guardDown {
    some s: Square | {
        some s.down
        some s.cell
        s.down.cell = none or s.down.cell.value = s.cell.value
    }
}

/**
 * This guarantees that the cells on the board are all either merged or
 * stay on the board, with child nodes appearing appropriately for merging.
*/
pred mergeOrMaintain {
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
    // All cells in the new board had either themselves or both parents in 
    // the previous board
    all c: Square.cell' | {
        {not c in Square.cell} <=> {
            # {c.parents & Square.cell} = 2
        }
    }
}

/**
 * Guarantees that cells remain on the same row in the next state (or their 
 * children do). For use in either the right or left transition predicates.
*/
pred rowsPreserved {
    all c: Square.cell {
        // Location on the same row
        c in Square.cell' => {
            c.location -> c.location' in ^(right + left + iden)
        }
        // OR location of child in the same row
        c.child in Square.cell' => {
            c.location -> c.child.location' in ^(right + left + iden)
        }
    }
}

/**
 * Makes sure that, if two cells are next two each other with the same value,
 * and either left or right is swiped, the two will merge together. 
*/
pred rowsForceMerge {
    // This represents right adjacentcy modulo empty spaces in between. 
    let cellRight = {c1: Cell, c2: Cell | {
        c1 in Square.cell
        c2 in Square.cell
        c1.location -> c2.location in ^right
        no c3 : Square.cell {
            c1.location -> c3.location in ^right
            c3.location -> c2.location in ^right
        }
    }} | {
    all c : Square.cell {
        c.cellRight.value = c.value => {
            c not in Square.cell' or c.cellRight not in Square.cell'
        }
    }}
}

// See above
pred colsForceMerge {
    // This represents right adjacentcy modulo empty spaces in between. 
    let cellDown = {c1: Cell, c2: Cell | {
        c1 in Square.cell
        c2 in Square.cell
        c1.location -> c2.location in ^down
        no c3 : Square.cell {
            c1.location -> c3.location in ^down
            c3.location -> c2.location in ^down
        }
    }} | {
    all c : Square.cell {
        c.cellDown.value = c.value => {
            c not in Square.cell' or c.cellDown not in Square.cell'
        }
    }}
}

/**
 * See above.
*/ 
pred colsPreserved {
    all c: Square.cell {
        c in Square.cell' => {
            c.location -> c.location' in ^(up + down + iden)
        }
        c.child in Square.cell' => {
            c.location -> c.child.location' in ^(up + down + iden)
        }
    }
}

/**
 * Checks that the cells in a state are "up agains" the right wall, with no
 * free spaces to the right of cells. 
*/
pred rightPushed {
    all s: Square {
        some s.cell => {
            no s.right or some s.right.cell
        }
    }
}

// See above
pred leftPushed {
    all s: Square {
        some s.cell => {
            no s.left or some s.left.cell
        }
    }
}

// See above
pred upPushed {
    all s: Square {
        some s.cell => {
            no s.up or some s.up.cell
        }
    }
}

// See above
pred downPushed {
    all s: Square {
        some s.cell => {
            no s.down or some s.down.cell
        }
    }
}

// See above
pred swipeRight {
    guardRight
    rowsForceMerge
    next_state rightPushed
    mergeOrMaintain
    rowsPreserved

    let finalOrdering = {c1: Cell, c2: Cell | {
            c1 in Square.cell'
            c2 in Square.cell'
            c1.location' -> c2.location' in right
    }} | {

        all c1: Cell, c2: Cell {{
            c1 in Square.cell
            c2 in Square.cell
            c1.location -> c2.location in ^right
            no c3 : Square.cell {
                c1.location -> c3.location in ^right
                c3.location -> c2.location in ^right
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

// See above
pred swipeLeft {
    guardLeft
    rowsForceMerge
    next_state leftPushed
    mergeOrMaintain
    rowsPreserved

    let finalOrdering = {c1: Cell, c2: Cell | {
            c1 in Square.cell'
            c2 in Square.cell'
            c1.location' -> c2.location' in left
    }} | {

        all c1: Cell, c2: Cell {{
            c1 in Square.cell
            c2 in Square.cell
            c1.location -> c2.location in ^left
            no c3 : Square.cell {
                c1.location -> c3.location in ^left
                c3.location -> c2.location in ^left
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

// See above
pred swipeUp {
    guardUp
    colsForceMerge
    next_state upPushed
    mergeOrMaintain
    colsPreserved

    let finalOrdering = {c1: Cell, c2: Cell | {
            c1 in Square.cell'
            c2 in Square.cell'
            c1.location' -> c2.location' in up
    }} | {

        all c1: Cell, c2: Cell {{
            c1 in Square.cell
            c2 in Square.cell
            c1.location -> c2.location in ^up
            no c3 : Square.cell {
                c1.location -> c3.location in ^up
                c3.location -> c2.location in ^up
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

// See above
pred swipeDown {
    guardDown
    colsForceMerge
    next_state downPushed
    mergeOrMaintain
    colsPreserved

    let finalOrdering = {c1: Cell, c2: Cell | {
            c1 in Square.cell'
            c2 in Square.cell'
            c1.location' -> c2.location' in down
    }} | {

        all c1: Cell, c2: Cell {{
            c1 in Square.cell
            c2 in Square.cell
            c1.location -> c2.location in ^down
            no c3 : Square.cell {
                c1.location -> c3.location in ^down
                c3.location -> c2.location in ^down
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
pred traces {
    fourByFour
    ordered
    cellWellFormed
    parenthoodWellFormed
    init
    always {
        swipeRight or swipeLeft or swipeUp or swipeDown or doNothing
    }
}

run {
    traces
    swipeRight
    next_state swipeDown
    (Board.squares[0][0]).cell.value = 1
    (Board.squares[2][0]).cell.value = 1
    (Board.squares[0][2]).cell.value = 1
    (Board.squares[2][2]).cell.value = 1
} for exactly 9 Square, 7 Cell