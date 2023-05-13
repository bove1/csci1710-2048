#lang forge "final" "nvliavoez7ahtpvr"

open "2048.frg"
open "2048.test.frg"

test expect {
  tracesSAT: { traces[4] } for optimizer4
    is sat




  // -- TODO: Validate that there is a trace where, at some point, every Smith is holding its left Chopstick. 
  // allHoldingSAT: { (traces) and (allHoldingLeft) } for exactly 5 Smith, exactly 5 Chopstick, 4 Int for optimizer
  //   is sat
  // -- TODO: Validate that we *can't* get stuck in the above case in polite smiths. 
  // getStuckUNSAT: { (traces) and (getStuck) } for exactly 5 Smith, exactly 5 Chopstick, 4 Int for optimizer
  //   is unsat


  -- Full game-play properties
  -- TODO: how fast can someone lose the game?
  -- TODO: how fast can someone reach the numbet 16?

  -- Configurations that can/cannot be reached from the initial state in a given number of moves
  -- TODO: Can the board have only 4 tiles, all on the corners?
  -- TODO: Can the board have 4 tiles, all the same number, in a 4x4 subgrid?
    // What about other arrangements of the same numbers? Ie as a Tetris piece or another size sub grid. 
  -- TODO: How many consecutive swipes right can the model support, given that the bottom row changes after each swipe?
  -- TODO: Suppose we can start with an arbitrary number of squares on the board (instead of just 2), how fast/can we reach 32? 
  -- TODO: Can we reach any state in which none of the cells are directly adjacent to each other? 
}


