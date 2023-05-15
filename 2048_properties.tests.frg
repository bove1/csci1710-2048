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
    always {#{Cell}>0}
}

-- the board should never be identical before and after a move
pred boardChanges {
   swipe => not (Board' = Board)
}

-- after a number appears, there must always be a cell with a value greater than or equal to it



-- after the squares are all filled and all adjacent cells have different values, 
-- the game is stuck and can not do anything 
-- lose condition
pred gameStuck[size: Int] {
    #{Square.cell} = Square
    // for any two coordinates, such that the coordinates are on the board
    all row1, col1, row2, col2 : Int | ((row1 != row2 or col1 != col2) 
        and (onTheBoard[row1, size]) and (onTheBoard[col1, size]) 
        and (ontheBoard[row2,size]) and (onTheBoard[col2,size])) implies {
        // 

    let row_dif = absDifference[row1,row2] | {
      let col_dif = absDifference[col1,col2] | {
        ((row_dif = col_dif) or (row_dif = 0) or (col_dif = 0) ) implies {
          not (some Board.position[row1][col1] and some Board.position[row2][col2])
        }
      } 
    }
  }
}

pred 

pred onTheBoard[coord: Int, size: Int] {
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
    eventually { 
        some c1, c2, c3, c4 : Cell | {
            c1.value = c2.value and c2.value = c3.value and c3.value = c4.value
        }
    }
}

-- the board should not be able to have only four cells, one on each corner
pred fourCorners[size: Int] {
    eventually {
        #{Cell} = 4
        some b : Board | {
            some (Board.squares[0][0]).cell
            some (Board.squares[0][size-1]).cell
            some (Board.squares[size-1][0]).cell
            some (Board.squares[size-1][size-1]).cell
        }
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
    eventually {
        #{Cell} = 3
        some b : Board | {
            some (Board.squares[0][0]).cell
            some (Board.squares[0][size-1]).cell
            some (Board.squares[size-1][0]).cell
        }
    }
}

-- the board should be able to have two cells on diagonally opposing corners
pred twoCorners[size: Int] {
    eventually {
        #{Cell} = 4
        some b : Board | {
            some (Board.squares[0][0]).cell
            some (Board.squares[0][size-1]).cell
            some (Board.squares[size-1][0]).cell
            some (Board.squares[size-1][size-1]).cell
        }
    }
}

-- the board should be able to have two cells on adjacent corners

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
        for optimizer3 is theorem
        
    tracesSAT4: { traces[4] } 
        for optimizer4 is theorem

    increasesAtSomePoint: { traces[4] implies increaseEventually } 
        for optimizer4 is theorem

    boardIsNeverEmpty: { traces[4] implies neverEmpty }
        for optimizer4 is theorem

    

    canHave4OfSameTile: {traces[4] and monozygoticSiblings } 
        for optimizer4 is sat
    
    tilesOnAllCorners: { traces[4] and fourCorners[4] }
        for optimizer4 is unsat

    tilesOnThreeCorners: { traces[4] and threeCorners[4] }
        for optimizer4 is sat

    tilesOnTwoCorners: { traces[4] and twoCorners[4] }
        for optimizer4 is sat

    
}   




  



