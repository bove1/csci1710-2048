#lang forge "dining_smiths/polite_smiths" "<anonymous email>"

option problem_type temporal
option max_tracelength 25
option min_tracelength  2

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

    var location: one Square
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
 General well-formedness conditions of the relationship between squares and cells.
*/
pred cellWellFormed {
    // .cell is injective where it exists
    all disj s1, s2: Square {
        s1.cell != s2.cell or s1.cell = none
    }

    // No self-parenthood
    no iden & parents

    // location is inverse as expected
    all c: Cell {
        c in Square.cell => {
            c.location.cell = c
        } else {
            no c.location
        }

        // Either one parent or no parents
        #{c.parents} = 0 or #{c.parents} = 2

        // Parent/child inverse property
        some c.child => {
            c in c.child.parents
            c.child.value = c.value + 1
        }

        // Other direction
        some c.parents => {
            c.parents.child = c
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

pred mergeOrMaintain {
    // All cells in the board keep either themselves or a child in the 
    // new board, but not both
    all c: Square.cell | {
        c in Square.cell' or c.child in Square.cell'
        not (c in Square.cell' and c.child in Square.cell')
    }
    // All cells in the new board had either themselves or both parents in 
    // the previous board
    all c: Square.cell' | {
        c in Square.cell or c.parents in Square.cell
        not (c in Square.cell and c.parents in Square.cell)
    }
}

// pred swipeRight {

//     all s: Square | {
//         some s.cell' => {
//             s.right = none or some s.right.cell'
//         }
//     }

//     let cells_order = {c1 : Cell, c2: Cell | {
//         c1 in Square.cell
//         c2 in Square.cell
//         c1.location -> c2.location in ^right

//         no c3 : Square.cell {
//             c1 -> c3 in ^right
//             c3 -> c2 in ^right
//         }
//     }} | {
    
//     all c: Square.cell | {
//         {
//             not {
//                 c in Square.cell'
//                 c.location -> c.location' in ^(left + right + iden)
//             }
//         } <=> {
//             some c.child
//             c.child in Square.cell'
//             c.cells_order in c.child.parents or c.(~cells_order) in c.child.parents
//             c.child.location' -> c.location in ^(left + right + iden)
//         }
//     }

//     let merge_order = {c1: Cell, c2: Cell | {
//         c1 in Square.cell'
//         c2 in Square.cell'
//         c1.location' -> c2.location' in right
//     }} | {

//     all disj c1, c2: Cell | {
//         {
//             c1 -> c2 in cells_order
//         } => {
//             {
//                 c1 -> c2 in merge_order
//             } or {
//                 some c1.child
//                 c1.child -> c2 in merge_order
//             } or {
//                 some c2.child
//                 c1 -> c2.child in merge_order
//             } or {
//                 some c1.child
//                 some c2.child
//                 c1.child -> c2.child in merge_order
//             } or {
//                 some c1.child
//                 c1.child = c2.child
//             }
//         }
//     }

//     }}
// }

run {
    fourByFour
    ordered
    always cellWellFormed
    init
    guardRight
    mergeOrMaintain
} for exactly 9 Square