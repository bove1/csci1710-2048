#lang forge "dining_smiths/polite_smiths" "<anonymous email>"

option problem_type temporal
option max_tracelength 25
option min_tracelength 1

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
    value : one Int // Values constant during cell's lifetime
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
 * There is a valid board.
 * All of the boxes are empty save for two (which have the lowest 
 * denomination -- the same that appear on a turn)
 */
pred init {
    // No rogue cells
    Cell in Square.cell

    // .cell is injective where it exists
    all disj s1, s2: Square {
        s1.cell != s2.cell or s1.cell = none
    }

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

run {
    fourByFour
    ordered
    init
} for exactly 9 Square