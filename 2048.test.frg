#lang forge "forge3/stop_and_copy.tests" "<anonymous email>"

open "2048.frg"

test expect {
    // twoByTwo: {
    //     fourByFour[2] => {
    //         #Square = 4
    //         some Board.squares[0][1]
    //         some Board.squares[1][0]
    //         no Board.squares[0][2]
    //         no Board.squares[2][0]
    //     }
    // } for 16 Square is theorem

    // threeByThree: {
    //     fourByFour[3] => {
    //         #Square = 9
    //         some Board.squares[0][1]
    //         some Board.squares[1][0]
    //         some Board.squares[0][2]
    //         some Board.squares[2][0]
    //         no Board.squares[3][0]
    //         no Board.squares[0][3]
    //     }
    // } for 16 Square is theorem

    // fourByFour: {
    //     fourByFour[4] => {
    //         #Square = 9
    //         some Board.squares[0][1]
    //         some Board.squares[1][0]
    //         some Board.squares[0][3]
    //         some Board.squares[3][0]
    //         no Board.squares[4][0]
    //         no Board.squares[0][4]
    //     }
    // } for 16 Square is theorem

    // orderedTest: {
    //     ordered[4] => {
    //         all dir: Direction {
    //             #(dir.ord) = 12
    //             #{s: Square | no s.dir} = 4
    //         }
    //     }
    // } for 16 Square is theorem

    // pushedRightTest: {
    //     {
    //         pushed[Right]
    //         fourByFour[4]
    //         ordered
    //         cellWellFormed
    //         some (Board.squares[0][0]).cell
    //         some (Board.squares[2][3]).cell
    //         no (Board.squares[2][2]).cell
    //     } => {
    //         some (Board.squares[1][0]).cell
    //         some (Board.squares[2][0]).cell
    //         some (Board.squares[3][0]).cell
    //         // Cells to right of 2, 3
    //         some (Board.squares[3][3]).cell
    //         // No cells to left of 2, 2
    //         no (Board.squares[0][2]).cell
    //         no (Board.squares[1][2]).cell
    //     } 
    // }for 16 Square, 16 Cell is theorem 

    // pushedUpTest: {
    //     wellFormed[4]
    //     some (Board.squares[0][0]).cell
    //     some (Board.squares[2][3]).cell
    //     no (Board.squares[2][2]).cell
    // }  for 16 Square, 16 Cell is unsat 

    // guardTest1: {
    //     {
    //         wellFormed[4]
    //         guard[Right]
    //         guard[Left]
    //         guard[Up]
    //         guard[Down]
    //         #(Square.cell) = 1
    //     } => {
    //         some Board.squares[1][1] or some Board.squares[1][2] or 
    //         some Board.squares[2][1] or some Board.squares[2][2]
    //     }
    // } for 16 Square, 1 Cell is theorem

    // LockoutTest: {
    //     {
    //         wellFormed[3]
    //         (Board.squares[0][0]).cell.value = 1
    //         (Board.squares[1][0]).cell.value = 0
    //         (Board.squares[2][0]).cell.value = 1
    //         (Board.squares[0][1]).cell.value = 0
    //         (Board.squares[1][1]).cell.value = 1
    //         (Board.squares[2][1]).cell.value = 0
    //         (Board.squares[0][2]).cell.value = 1
    //         (Board.squares[1][2]).cell.value = 0
    //         (Board.squares[2][2]).cell.value = 1
    //     } => {
    //         no dir: Direction | {guard[dir]}
    //     }
    // }for 9 Square, 9 Cell is theorem 

    // rowColPreservedTest: {
    //     // Right and left are equivalent
    //     wellFormed[4] => {
    //         { 
    //             rowColPreserved[Right]
    //         } <=> {
    //             rowColPreserved[Left]
    //         }
    //         {
    //             rowColPreserved[Up]
    //         } <=> {
    //             rowColPreserved[Down]
    //         }

    //         all c: Square.cell {
    //             {
    //                 some c.child and c.child in Square.cell'
    //                 rowColPreserved[Down]
    //                 (Board.squares[0][0]).cell.value = c
    //             } => {
    //                 c.child in (Board.squares[0][Int]).cell.value
    //             }
    //         }
    //     }
    // } for 16 Square, 5 Cell is theorem 
}