#lang forge "final" "nvliavoez7ahtpvr@gmail.com"

// Observing full-game properties of 2x2 grids. 
//     How fast can someone lose the game? 
//     How fast can they reach the number 16?
// Observing more “local” properties on a 4x4 grid, ie configurations that can/cannot be reached from the initial state in a given number of moves. 
//     Can the board have only 4 tiles, all on the corners?
//     Can the board have 4 tiles, all the same number, in a 4x4 subgrid?
//     What about other arrangements of the same numbers? Ie as a Tetris piece or another size sub grid. 
//     How many consecutive swipes right can the model support, given that the bottom row changes after each swipe?
//     Suppose we can start with an arbitrary number of squares on the board (instead of just 2), how fast/can we reach 32? 
//     Can we reach any state in which none of the cells are directly adjacent to each other? 
