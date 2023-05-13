#lang forge "final" "nvliavoez7ahtpvr"

open "2048.frg"
// option solver Glucose
option problem_type temporal
option max_tracelength 2
option min_tracelength 1

/**
 * Potential optimizer for the board.
 */ 
inst optimizer4 {
    Board = `Board
    Square =    `Square00 + `Square10 + `Square20 + `Square30 +
                `Square01 + `Square11 + `Square21 + `Square31 +
                `Square02 + `Square12 + `Square22 + `Square32 +
                `Square03 + `Square13 + `Square23 + `Square33 

    squares = Board -> (
        0 -> (0 -> `Square00 + 1 -> `Square01 + 2 -> `Square02 + 3 -> `Square03) + 
        1 -> (0 -> `Square10 + 1 -> `Square11 + 2 -> `Square12 + 3 -> `Square13) + 
        2 -> (0 -> `Square20 + 1 -> `Square21 + 2 -> `Square22 + 3 -> `Square23) + 
        3 -> (0 -> `Square30 + 1 -> `Square31 + 2 -> `Square32 + 3 -> `Square33) 
    )
    
    Right = `Right
    Left =  `Left
    Up =    `Up
    Down =  `Down
    Direction = Right + Left + Up + Down
    ord = `Right -> (
        `Square00 -> `Square10 + `Square10 -> `Square20 + `Square20 -> `Square30 + 
        `Square01 -> `Square11 + `Square11 -> `Square21 + `Square21 -> `Square31 + 
        `Square02 -> `Square12 + `Square12 -> `Square22 + `Square22 -> `Square32 + 
        `Square03 -> `Square13 + `Square13 -> `Square23 + `Square23 -> `Square33 
    ) + `Left -> (
        `Square30 -> `Square20 + `Square20 -> `Square10 + `Square10 -> `Square00 + 
        `Square31 -> `Square21 + `Square21 -> `Square11 + `Square11 -> `Square01 + 
        `Square32 -> `Square22 + `Square22 -> `Square12 + `Square12 -> `Square02 + 
        `Square33 -> `Square23 + `Square23 -> `Square13 + `Square13 -> `Square03 
    ) + `Up -> (
        `Square03 -> `Square02 + `Square02 -> `Square01 + `Square01 -> `Square00 + 
        `Square13 -> `Square12 + `Square12 -> `Square11 + `Square11 -> `Square10 + 
        `Square23 -> `Square22 + `Square22 -> `Square21 + `Square21 -> `Square20 + 
        `Square33 -> `Square32 + `Square32 -> `Square31 + `Square31 -> `Square30 
    ) + `Down -> (
        `Square00 -> `Square01 + `Square01 -> `Square02 + `Square02 -> `Square03 + 
        `Square10 -> `Square11 + `Square11 -> `Square12 + `Square12 -> `Square13 + 
        `Square20 -> `Square21 + `Square21 -> `Square22 + `Square22 -> `Square23 + 
        `Square30 -> `Square31 + `Square31 -> `Square32 + `Square32 -> `Square33 
    )
}

// run {} for 16 Square for optimizer4

test expect {
//     twoByTwo: {
//         fourByFour[2] => {
//             #Square = 4
//             some Board.squares[0][1]
//             some Board.squares[1][0]
//             no Board.squares[0][2]
//             no Board.squares[2][0]
//         }
//     } for 16 Square, 0 Cell is theorem

//     threeByThree: {
//         fourByFour[3] => {
//             some Board.squares[0][1]
//             some Board.squares[1][0]
//             some Board.squares[0][2]
//             some Board.squares[2][0]
//             no Board.squares[3][0]
//             no Board.squares[0][3]
//         }
//     } for exactly 9 Square, 0 Cell is theorem

//     fourByFour: {
//         fourByFour[4] => {
//             some Board.squares[0][1]
//             some Board.squares[1][0]
//             some Board.squares[0][3]
//             some Board.squares[3][0]
//             no Board.squares[4][0]
//             no Board.squares[0][4]
//         }
//     } for exactly 16 Square, 0 Cell is theorem

//     orderedTest: {
//         {ordered[4] and fourByFour[4]} => {
//             all dir: Direction {
//                 #(dir.ord) = 12
//                 #{s: Square | no s.(dir.ord)} = 4
//             }
//         }
//     } for exactly 16 Square, 0 Cell is theorem

    // orderedThm: {
    //     not ordered[4]
    // } for optimizer4 is theorem

    // pushedRightTest: {
    //     all c: Cell {
    //         {
    //             pushed[Right, c]
    //             wellFormed[4]
    //             some (Board.squares[0][0]).cell - c
    //             some (Board.squares[2][3]).cell - c
    //             no (Board.squares[2][2]).cell - c
    //         } => {
    //             some (Board.squares[1][0]).cell - c
    //             some (Board.squares[2][0]).cell - c
    //             some (Board.squares[3][0]).cell - c
    //             // Cells to right of 2, 3
    //             some (Board.squares[3][3]).cell - c
    //             // No cells to left of 2, 2
    //             no (Board.squares[0][2]).cell - c
    //             no (Board.squares[1][2]).cell - c
    //         } 
    //     }
    // } for optimizer4 is theorem 

//     pushedUpTest: {
//         wellFormed[4]
//         some (Board.squares[0][0]).cell
//         some (Board.squares[2][3]).cell
//         no (Board.squares[2][2]).cell
//     }  for 16 Square, 16 Cell is unsat 

//     guardTest1: {
//         {
//             wellFormed[4]
//             guard[Right]
//             guard[Left]
//             guard[Up]
//             guard[Down]
//             #(Square.cell) = 1
//         } => {
//             some Board.squares[1][1] or some Board.squares[1][2] or 
//             some Board.squares[2][1] or some Board.squares[2][2]
//         }
//     } for 16 Square, 1 Cell is theorem

//     LockoutTest: {
//         {
//             wellFormed[3]
//             (Board.squares[0][0]).cell.value = 1
//             (Board.squares[1][0]).cell.value = 0
//             (Board.squares[2][0]).cell.value = 1
//             (Board.squares[0][1]).cell.value = 0
//             (Board.squares[1][1]).cell.value = 1
//             (Board.squares[2][1]).cell.value = 0
//             (Board.squares[0][2]).cell.value = 1
//             (Board.squares[1][2]).cell.value = 0
//             (Board.squares[2][2]).cell.value = 1
//         } => {
//             no dir: Direction | {guard[dir]}
//         }
//     }for 9 Square, 9 Cell is theorem 

//     rowColPreservedTest: {
//         // Right and left are equivalent
//         wellFormed[4] => {
//             { 
//                 rowColPreserved[Right]
//             } <=> {
//                 rowColPreserved[Left]
//             }
//             {
//                 rowColPreserved[Up]
//             } <=> {
//                 rowColPreserved[Down]
//             }

//             all c: Square.cell {
//                 {
//                     some c.child and c.child in Square.cell'
//                     rowColPreserved[Down]
//                     (Board.squares[0][0]).cell.value = c
//                 } => {
//                     c.child in (Board.squares[0][Int]).cell.value
//                 }
//             }
//         }
//     } for 16 Square, 5 Cell is theorem 
}