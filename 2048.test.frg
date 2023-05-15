#lang forge "final" "nvliavoez7ahtpvr"

open "2048.frg"
// option solver Glucose
option problem_type temporal
option min_tracelength 1
option max_tracelength 2

/**
 * Optimizes a 4x4 board
 */ 
inst optimizer4 {
    Board = `Board0
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
    
    Right = `Right0
    Left =  `Left0
    Up =    `Up0
    Down =  `Down0
    Direction = Right + Left + Up + Down
    ord = `Right0 -> (
        `Square00 -> `Square10 + `Square10 -> `Square20 + `Square20 -> `Square30 + 
        `Square01 -> `Square11 + `Square11 -> `Square21 + `Square21 -> `Square31 + 
        `Square02 -> `Square12 + `Square12 -> `Square22 + `Square22 -> `Square32 + 
        `Square03 -> `Square13 + `Square13 -> `Square23 + `Square23 -> `Square33 
    ) + `Left0 -> (
        `Square30 -> `Square20 + `Square20 -> `Square10 + `Square10 -> `Square00 + 
        `Square31 -> `Square21 + `Square21 -> `Square11 + `Square11 -> `Square01 + 
        `Square32 -> `Square22 + `Square22 -> `Square12 + `Square12 -> `Square02 + 
        `Square33 -> `Square23 + `Square23 -> `Square13 + `Square13 -> `Square03 
    ) + `Up0 -> (
        `Square03 -> `Square02 + `Square02 -> `Square01 + `Square01 -> `Square00 + 
        `Square13 -> `Square12 + `Square12 -> `Square11 + `Square11 -> `Square10 + 
        `Square23 -> `Square22 + `Square22 -> `Square21 + `Square21 -> `Square20 + 
        `Square33 -> `Square32 + `Square32 -> `Square31 + `Square31 -> `Square30 
    ) + `Down0 -> (
        `Square00 -> `Square01 + `Square01 -> `Square02 + `Square02 -> `Square03 + 
        `Square10 -> `Square11 + `Square11 -> `Square12 + `Square12 -> `Square13 + 
        `Square20 -> `Square21 + `Square21 -> `Square22 + `Square22 -> `Square23 + 
        `Square30 -> `Square31 + `Square31 -> `Square32 + `Square32 -> `Square33 
    )
}

/**
 * Optimizes a 3x3 board
 */
inst optimizer3 {
    Board = `Board0
    Square =    `Square00 + `Square10 + `Square20 +
                `Square01 + `Square11 + `Square21 + 
                `Square02 + `Square12 + `Square22 

    squares = Board -> (
        0 -> (0 -> `Square00 + 1 -> `Square01 + 2 -> `Square02) + 
        1 -> (0 -> `Square10 + 1 -> `Square11 + 2 -> `Square12) + 
        2 -> (0 -> `Square20 + 1 -> `Square21 + 2 -> `Square22)
    )
    
    Right = `Right0
    Left =  `Left0
    Up =    `Up0
    Down =  `Down0
    Direction = Right + Left + Up + Down
    ord = `Right0 -> (
        `Square00 -> `Square10 + `Square10 -> `Square20 +
        `Square01 -> `Square11 + `Square11 -> `Square21 +
        `Square02 -> `Square12 + `Square12 -> `Square22 
    ) + `Left0 -> (
        `Square20 -> `Square10 + `Square10 -> `Square00 + 
        `Square21 -> `Square11 + `Square11 -> `Square01 + 
        `Square22 -> `Square12 + `Square12 -> `Square02 
    ) + `Up0 -> (
        `Square02 -> `Square01 + `Square01 -> `Square00 + 
        `Square12 -> `Square11 + `Square11 -> `Square10 + 
        `Square22 -> `Square21 + `Square21 -> `Square20 
    ) + `Down0 -> (
        `Square00 -> `Square01 + `Square01 -> `Square02 + 
        `Square10 -> `Square11 + `Square11 -> `Square12 +
        `Square20 -> `Square21 + `Square21 -> `Square22 
    )
}

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

    // orderedTest: {
    //     {ordered[4] and fourByFour[4]} => {
    //         all dir: Direction {
    //             #(dir.ord) = 12
    //             #{s: Square | no s.(dir.ord)} = 4
    //         }
    //     }
    // } for exactly 16 Square, 0 Cell is theorem

    optFourByFour4: {fourByFour[4]} for optimizer4 is theorem
    optFourByFour3: {fourByFour[3]} for optimizer3 is theorem
    optFourByFour4: {ordered[4]} for optimizer4 is theorem
    optFourByFour3: {ordered[3]} for optimizer3 is theorem

    pushedRightTest: {
        all c: Cell {
            {
                pushed[Right, c]
                wellFormed[4]
                some (Board.squares[0][0]).cell - c
                some (Board.squares[2][3]).cell - c
                no (Board.squares[2][2]).cell - c
            } => {
                some (Board.squares[1][0]).cell - c
                some (Board.squares[2][0]).cell - c
                some (Board.squares[3][0]).cell - c
                // Cells to right of 2, 3
                some (Board.squares[3][3]).cell - c
                // No cells to left of 2, 2
                no (Board.squares[0][2]).cell - c
                no (Board.squares[1][2]).cell - c
            } 
        }
    } for 7 Cell for optimizer4 is theorem 

    pushedRightTestSat: {
        some c: Cell {
            pushed[Right, c]
            wellFormed[4]
            some (Board.squares[0][0]).cell - c
            some (Board.squares[2][3]).cell - c
            no (Board.squares[2][2]).cell - c
        }
    } for 7 Cell for optimizer4 is sat

    pushedUpTest: {
        some c: Cell {
            pushed[Up, c]
            wellFormed[4]
            some (Board.squares[2][3]).cell - c
            no (Board.squares[2][2]).cell - c
        }
    }  for 7 Cell for optimizer4 is unsat 

    guardTest1: {
        {
            wellFormed[4]
            guard[Right]
            guard[Left]
            guard[Up]
            guard[Down]
            #(Square.cell) = 1
        } => {
            some Board.squares[1][1] or some Board.squares[1][2] or 
            some Board.squares[2][1] or some Board.squares[2][2]
        }
    } for optimizer4 is theorem

    guardTest1Sat: {
        wellFormed[4]
        guard[Right]
        guard[Left]
        guard[Up]
        guard[Down]
        #(Square.cell) = 1
    } for optimizer4 is sat

    LockoutTest: {
        {
            wellFormed[3]
            (Board.squares[0][0]).cell.value = 1
            (Board.squares[1][0]).cell.value = 0
            (Board.squares[2][0]).cell.value = 1
            (Board.squares[0][1]).cell.value = 0
            (Board.squares[1][1]).cell.value = 1
            (Board.squares[2][1]).cell.value = 0
            (Board.squares[0][2]).cell.value = 1
            (Board.squares[1][2]).cell.value = 0
            (Board.squares[2][2]).cell.value = 1
        } => {
            no dir: Direction | {guard[dir]}
        }
    }for 9 Square, 9 Cell for optimizer3 is theorem 

    LockoutTestSat: {
        wellFormed[3]
        (Board.squares[0][0]).cell.value = 1
        (Board.squares[1][0]).cell.value = 0
        (Board.squares[2][0]).cell.value = 1
        (Board.squares[0][1]).cell.value = 0
        (Board.squares[1][1]).cell.value = 1
        (Board.squares[2][1]).cell.value = 0
        (Board.squares[0][2]).cell.value = 1
        (Board.squares[1][2]).cell.value = 0
        (Board.squares[2][2]).cell.value = 1
    } for 9 Square, 9 Cell for optimizer3 is sat

    rowColPreservedTest: {
        // Right and left are equivalent
        wellFormed[4] => {
            { 
                rowColPreserved[Right]
            } <=> {
                rowColPreserved[Left]
            }
            {
                rowColPreserved[Up]
            } <=> {
                rowColPreserved[Down]
            }

            all c: Square.cell {
                {
                    some c.child and c.child in Square.cell'
                    rowColPreserved[Down]
                    (Board.squares[0][0]).cell.value = c
                } => {
                    c.child in (Board.squares[0][Int]).cell.value
                }
            }
        }
    } for 16 Square, 5 Cell for optimizer4 is theorem 

    mergeOrMaintainTest: {
        all c: Cell | {{mergeOrMaintain[c] and wellFormed[4]} => {
            c not in Square.cell // Added not in original
            c in Square.cell' // Added in new
            #{Square.cell} >= #{Square.cell' - c} // Number of non-added cells goes down or equal

            all c2: Square.cell' - c{
                c2 in Square.cell or {some c2.parents and c2.parents in Square.cell} // Either from original, or parents are in it
                not (c2 in Square.cell and {some c2.parents and c2.parents in Square.cell})
            }
        }}
    } for 16 Square, 8 Cell for optimizer4 is theorem

    mergeOrMaintainTestSat: {
        some c: Cell | {mergeOrMaintain[c] and wellFormed[4]}
    } for 16 Square, 8 Cell for optimizer4 is sat

    forceMergeTest1: {
        {
            wellFormed[4]
            forceMerge[Right]
            // forceMerge assumes mergeOrMaintain
            some c: Cell | mergeOrMaintain[c] 
            // Also rowColPreserved
            rowColPreserved[Right]

            // First row
            (Board.squares[0][0]).cell.value = 1
            (Board.squares[1][0]).cell.value = none
            (Board.squares[2][0]).cell.value = none
            (Board.squares[3][0]).cell.value = 1
        } => {
            // First row results
            some (Board.squares[0][0]).cell.child
            (Board.squares[0][0]).cell.child = (Board.squares[3][0]).cell.child
            (Board.squares[0][0]).cell.child in Square.cell'
        }
    } for 16 Square, 5 Cell for optimizer4 is theorem

    forceMergeTest1Sat: {
        wellFormed[4]
        forceMerge[Right]
        some c: Cell | mergeOrMaintain[c] // forceMerge assumes mergeOrMaintain
        // First row
        (Board.squares[0][0]).cell.value = 1
        (Board.squares[1][0]).cell.value = none
        (Board.squares[2][0]).cell.value = none
        (Board.squares[3][0]).cell.value = 1

    } for 16 Square, 5 Cell for optimizer4 is sat

    forceMergeTest2: {
        {
            wellFormed[4]
            forceMerge[Down]
            // forceMerge assumes mergeOrMaintain
            some c: Cell | mergeOrMaintain[c] 
            // Also rowColPreserved
            rowColPreserved[Down]

            // Second col 
            (Board.squares[1][0]).cell.value = 2
            (Board.squares[1][1]).cell.value = 2
            (Board.squares[1][2]).cell.value = none
            (Board.squares[1][3]).cell.value = 2
        } => {
            // Second col results
            some (Board.squares[1][3]).cell.child
            (Board.squares[1][3]).cell.child = (Board.squares[1][1]).cell.child
            (Board.squares[1][3]).cell.child in Square.cell'
            no (Board.squares[0][1]).cell.child or (Board.squares[0][1]).cell.child not in Square.cell'
        }
    } for 16 Square, 5 Cell for optimizer4 is theorem

    forceMergeTest2Sat: {
        wellFormed[4]
        forceMerge[Down]
        // forceMerge assumes mergeOrMaintain
        some c: Cell | mergeOrMaintain[c] 
        // Also rowColPreserved
        rowColPreserved[Down]

        // Second col 
        (Board.squares[1][0]).cell.value = 2
        (Board.squares[1][1]).cell.value = 2
        (Board.squares[1][2]).cell.value = none
        (Board.squares[1][3]).cell.value = 2
    } for 16 Square, 5 Cell for optimizer4 is sat

    forceMergeTest3: {
        {
            wellFormed[4]
            forceMerge[Left]
            // forceMerge assumes mergeOrMaintain
            some c: Cell | mergeOrMaintain[c] 
            // Also rowColPreserved
            rowColPreserved[Left]

            // Third row 
            (Board.squares[0][2]).cell.value = 1
            (Board.squares[1][2]).cell.value = 1
            (Board.squares[2][2]).cell.value = 1
            (Board.squares[3][2]).cell.value = 1
        } => {
            // Third row results
            some (Board.squares[2][2]).cell.child
            some (Board.squares[1][2]).cell.child
            (Board.squares[0][2]).cell.child in Square.cell'
            (Board.squares[2][2]).cell.child in Square.cell'
        }
    } for 16 Square, 7 Cell for optimizer4 is theorem

    forceMergeTest3Sat: {
        wellFormed[4]
        forceMerge[Left]
        // forceMerge assumes mergeOrMaintain
        some c: Cell | mergeOrMaintain[c] 
        // Also rowColPreserved
        rowColPreserved[Left]

        // Third row 
        (Board.squares[0][2]).cell.value = 1
        (Board.squares[1][2]).cell.value = 1
        (Board.squares[2][2]).cell.value = 1
        (Board.squares[3][2]).cell.value = 1
    } for 16 Square, 7 Cell for optimizer4 is sat

    swipeTest1: {
        {
            wellFormed[4]
            some c: Cell | swipe[Down, c]
            (Board.squares[0][0]).cell.value = 1
            (Board.squares[0][1]).cell.value = none
            (Board.squares[0][2]).cell.value = 1
            (Board.squares[0][3]).cell.value = 2
        } => {
            (Board.squares[0][2]).cell'.value = 2
            (Board.squares[0][3]).cell'.value = 2
        }
    } for 16 Square, 7 Cell for optimizer4 is theorem

    swipeTest1Sat: {
        wellFormed[4]
        some c: Cell | swipe[Down, c]
        (Board.squares[0][0]).cell.value = 1
        (Board.squares[0][1]).cell.value = none
        (Board.squares[0][2]).cell.value = 1
        (Board.squares[0][3]).cell.value = 2
    } for 16 Square, 7 Cell for optimizer4 is sat

    swipeTest2: {
        {
            wellFormed[4]
            some c: Cell | swipe[Down, c]
            (Board.squares[0][0]).cell.value = 1
            (Board.squares[0][1]).cell.value = 2
            (Board.squares[0][2]).cell.value = 2
            (Board.squares[0][3]).cell.value = 2
        } => {
            (Board.squares[0][1]).cell'.value = 1
            (Board.squares[0][2]).cell'.value = 2
            (Board.squares[0][3]).cell'.value = 3
        }
    } for 16 Square, 7 Cell for optimizer4 is theorem

    swipeTest2: {
        wellFormed[4]
        some c: Cell | swipe[Down, c]
        (Board.squares[0][0]).cell.value = 1
        (Board.squares[0][1]).cell.value = 2
        (Board.squares[0][2]).cell.value = 2
        (Board.squares[0][3]).cell.value = 2
    } for 16 Square, 7 Cell for optimizer4 is sat
}