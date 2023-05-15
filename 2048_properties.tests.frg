#lang forge "final" "nvliavoez7ahtpvr"

open "2048.frg"
open "2048.test.frg"

/*-------------------------------------*\
|       2048 Procedure Descriptions     |
\*-------------------------------------*/

-- at some point in every game (where there's movement) there should be an increase in cell value
pred increaseEventually {
    eventually { some c : Cell | {c.value = 2}}
}

-- the board should never be empty
pred neverEmpty {
    always { #{Square.cell} > 0 }
}

-- the board should never be identical before and after a move
pred boardChanges {
    always {
        some d: Direction, c: Cell | {
            swipe[d,c] => not (Square.cell' = Square.cell)
        }
    }
}

-- after a number appears, there must always be a cell with a value greater than or equal to it



-- after the squares are all filled and all adjacent cells have different values, 
-- the game is stuck and can not do anything 
-- lose condition
pred gameStuck[size: Int] {
    #{Square.cell} = Square
    // for any two coordinates, such that the coordinates are unique...
    all c1, r1, c2, r2 : Int | ((r1 != r2 or c1 != c2) 
    // ...and on the board...
        and (onTheBoard[c1,r1,c2,r2,size]) 
    // ...and all adjacent cells have different values...
        and differentAdjacent[c1,r1,c2,r2]) implies {
    // the game is now stuck
        always {
            Board' = Board
        }
    }
}

pred differentAdjacent[c1 : Int, r1: Int, c2: Int, r2: Int] {
    let row_dif = absDifference[r1,r2] | {
      let col_dif = absDifference[c1,c2] | {
        //they are adjacent
        ((row_dif = col_dif) or (row_dif = 0) or (col_dif = 0)) and
        //they have different values
        (not ((Board.squares[c1][r1]).cell.value = (Board.squares[c2][r2]).cell.value))
      } 
    }
}

pred onTheBoard[c1: Int, r1: Int, c2: Int, r2: Int, size: Int] {
    validCoord[c1, size] and validCoord[r1, size] and validCoord[c2, size] and validCoord[r2, size]
}

pred validCoord[coord: Int, size: Int] {
    (coord > 0) and (coord < size)
}

fun absDifference(m: Int, n: Int): Int {
  let difference = subtract[m, n] {
    difference > 0 => difference else subtract[0, difference]
  }
}

-- Can the board have 4 tiles, all the same number, in a 4x4 subgrid?
-- Yes
pred monozygoticSiblings {
    some c1, c2, c3, c4 : Cell | {
        c1 in Square.cell
        c2 in Square.cell
        c3 in Square.cell
        c4 in Square.cell

        c1.value = c2.value
        c2.value = c3.value 
        c3.value = c4.value
    }
}

-- the board should not be able to have only four cells, one on each corner
pred fourCorners[size: Int] {
    #{Square.cell} = 4
    some b : Board | {
        // (Board.squares).(cell.location) = col -> row
        // ((Board.squares).(cell.location)).Int = col
        // Int.((Board.squares).(cell.location)) = row
        some (Board.squares[0][0]).cell
        some (Board.squares[0][size-1]).cell
        some (Board.squares[size-1][0]).cell
        some (Board.squares[size-1][size-1]).cell
    }
}

-- the board should be able to have three cells, one on each corner
-- it takes some very specific cell generation (on the corners) but it should be possible
pred threeCorners[size: Int] {
/*
    1 0 0 0
    0 0 0 0
    0 0 0 0
    1 0 0 0
    (right, one generates in a corner)
    1 0 0 1
    0 0 0 0
    0 0 0 0
    0 0 0 1
 */
    #{Square.cell} = 3
    some b : Board | {
        // not [0][0]
        ((some (Board.squares[0][size-1]).cell
        and some (Board.squares[size-1][0]).cell
        and some (Board.squares[size-1][size-1]).cell) 
        or
        // not [0][size-1]
        (some (Board.squares[0][0]).cell
        and some (Board.squares[size-1][0]).cell
        and some (Board.squares[size-1][size-1]).cell)
        or
        // not [size-1][0]
        (some (Board.squares[0][0]).cell
        and some (Board.squares[0][size-1]).cell
        and some (Board.squares[size-1][size-1]).cell)
        or
        // not [size-1][size-1]
        (some (Board.squares[0][0]).cell
        and some (Board.squares[0][size-1]).cell
        and some (Board.squares[size-1][0]).cell))
    }
}

-- the board should be able to have two cells on diagonally opposing corners
pred twoDiagonalCorners[size: Int] {
    #{Square.cell} = 2
    some b : Board | {
        ((some (Board.squares[0][0]).cell and some (Board.squares[size-1][size-1]).cell)
        or
        (some (Board.squares[0][size-1]).cell and some (Board.squares[size-1][0]).cell))
    }
}

-- the board should be able to have two cells on adjacent corners
pred twoAdjacentCorners[size: Int] {
    #{Square.cell} = 2
    some b : Board | {
        ((some (Board.squares[0][0]).cell and some (Board.squares[0][size-1]).cell) 
        or
        (some (Board.squares[0][size-1]).cell and some (Board.squares[size-1][size-1]).cell)
        or 
        (some (Board.squares[size-1][size-1]).cell and some (Board.squares[size-1][0]).cell)
        or
        (some (Board.squares[size-1][0]).cell and some (Board.squares[0][0]).cell))
    }
}

// What about other arrangements of the same numbers? Ie as a Tetris piece or another size sub grid. 
// Tetris comes after I figure out how the location system works

-- TODO: How many consecutive swipes [left] can the model support, given that the bottom row changes after each swipe?
/* 
Probably 11?
1111
22_1
31_1
32_1
3211
3221
3311
42_1
4211
4221
4311
4321
*/


test expect {
    tracesSAT3: { traces[3] } 
        for optimizer3 is sat
        
    tracesSAT4: { traces[4] } 
        for optimizer4 is sat

    increasesAtSomePoint: { traces[4] and increaseEventually } 
        for optimizer4 is sat

    boardIsNeverEmpty: { traces[4] implies neverEmpty }
        for optimizer4 is theorem

    boardChangesAfterMove: {traces[4] implies boardChanges }
        for optimizer4 is theorem
    
    loseGamePossible: { traces[2] and gameStuck[2] }
        for optimizer2 is sat

    canHave4ofSameTile: {traces[4] and monozygoticSiblings } 
        for optimizer4 is sat
    
    tilesOnAllCorners: { traces[4] and fourCorners[4] }
        for optimizer4 is unsat

    tilesOnThreeCorners: { traces[4] and threeCorners[4] }
        for optimizer4 is sat

    tilesOnTwoCorners: { traces[4] and twoDiagonalCorners[4] }
        for optimizer4 is sat

    tilesOnTwoCorners: { traces[4] and twoAdjacentCorners[4] }
        for optimizer4 is sat

    
}   




  



