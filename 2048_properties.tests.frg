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
        #{Square.cell} = 4
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
        #{Square.cell} = 3
        some b : Board | {
            some (Board.squares[0][0]).cell
            some (Board.squares[0][size-1]).cell
            some (Board.squares[size-1][0]).cell
        }
    }
}

-- the board should be able to have two cells, one on each corner
pred twoCorners[size: Int] {
    eventually {
        #{Square.cell} = 4
        some b : Board | {
            some (Board.squares[0][0]).cell
            some (Board.squares[0][size-1]).cell
            some (Board.squares[size-1][0]).cell
            some (Board.squares[size-1][size-1]).cell
        }
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
        for optimizer3 is theorem
        
    tracesSAT4: { traces[4] } 
        for optimizer4 is theorem

    increasesAtSomePoint: { traces[4] implies increaseEventually } 
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




  



