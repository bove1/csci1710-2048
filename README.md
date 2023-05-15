# Modelling 2048 in Forge

#### Ethan Bove (), Valentina Lin (vlin10)

The goal of this project was to model the classic game 2048 using Forge.

[CSCI 1710: Spring 2023](https://csci1710.github.io//2023/)
|
[GitHub](https://github.com/bove1/csci1710-2048)
|
[Forge](https://csci1710.github.io/forge-documentation/home.html)

_With special thanks to [Tim Nelson](https://github.com/tnelson/Forge/tree/main)._

---

## User Guide

---

## Overview of the model

### Sigs

The two key sigs used in the project are `Square` and `Cell`. Squares represent the individual locations on the board (in the 4x4 case, 16 of them), whereas the cells represent the blocks that show up in those cells. Importantly, cells also have `child` and `parents` fields, keeping track of what cells formed (or will be formed) from the given cell. 

On top of these, we also have the abstract sig `Direction` with one sig implementations for each of the directions the user can swipe in the game. 

This representation came after a few messier solutions. Originally, we hoped to represent the game using only Cells, with vacancies represented as intentional holes in the `Board`'s square function. The `Direction` sig was another late addition. All transition predicates were originally written in four different ways. Not only does the `Direction` sig save space, but it also allows for generalization to more directions (like forward or backward for 3d).

### Predicates

The first few predicates all check well-formedness of the underlying structure of the model. For instance, the `ordered` predicate checks that the orderings designated by `Direction` sigs matches what the user expects. Other facts include checking that `parent` forms a series of binary trees. 

We then move onto our transition predicates. Because the basic transition predicate `swipe` includes a lot of information, it is broken into a number of smaller predicates. While more detailed information about each of these predicates can be seen in the model, here's a brief overview of each:
 - `guard[dir]` is a typical guard predicate for whether a swipe can be taken.
 - `mergeOrMaintain[new]` checks that the content of the complete content of the board changes as expected (either the same or merging, along with addition of our new cell).
 - `rowColPreserved[dir]` checks that cells stay on the same row or column. 
 - `pushed[dir]` confirms that cells are "up against the wall" as expected in the following state.
 - `forceMerge[dir]` requires that a cell merges if it is possible to. 
 - `swipe[dir]`, along with implementing the above predicates, also checks that the order in a certain direction is preserved after swiping. 

 This strict separation of requirements was the result of a much more lax original plan. At first, all the above sigs were bundled together into `swipe` alone. While a good idea on the surface, this quickly became far more confusing. Our new implementation also has the benefit of significantly easier unit testing. 

 We also made a later change to account for variable board sizing. Where relevant, predicates will have a `size: Int` parameter, which determines the size of the board that the user will generate. Most testing is done on a 4x4 grid, but there are a few instances where 3x3 and 2x2 boards are more insightful (and who's statespace can be searched by forge in a timely manner). 
 
---

## Visualization

As with most Forge models, the graph and table view are virtually useless. Thus, we provide a custom visualization for the data. To use the vis script, simply paste it from the `2048.frg` file into the document 

---

## Properties of the Game

- At some point in every game, provided there is directional movement, there should be an increase in cell value
- The board cannot at any point have only four Cells, one on each corner
- It (should be) possible to have only three Cells, on three of the four corners
  - Similarly, it should be possible to have only two Cells, both on diagonally opposing and adjacent corners

---

## Development Process

We started the project with the intent of 

---


