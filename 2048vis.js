boardSize = 3
count = 0
stage = new Stage()

const colors = {
    1: "#ede4da",
    2: "#ede0c8",
    3: "#f1b179",
    4: "#f59562",
    5: "#f57c5f"
}

for (inst of instances) {
    console.log(inst)
    board = inst.signature('Board')
    cell = inst.field('cell')

    let gridProps = {
        grid_location: {x: 40 + 40 * count * (boardSize + 1), y: 40},
        cell_size:{
            x_size: 40,
            y_size: 40
        },
        grid_dimensions:{
            x_size: boardSize,
            y_size: boardSize
        }
    }

    let grid = new Grid(gridProps)

    for (let c = 0; c < boardSize; c++) {
        for (let r = 0; r < boardSize; r++) {
            let tuples = board.squares.tuples()

            for (t of tuples){
                atoms = t.atoms()
                if (atoms[0].id() == c && atoms[1].id() == r) {
                    let v = atoms[2].join(cell).tuples()[0]
                    if (v != undefined) {
                        let squareProps = {
                            coords: {x: 100, y:100},
                            height: 30,
                            width: 30,
                            color: colors[v.join(value).tuples()[0].atoms()[0].id().toString()],
                            label: 2**v.join(value).tuples()[0].atoms()[0].id().toString()
                        };
                        let square = new Rectangle(squareProps)
                        grid.add({x: c, y: r}, square)
                    }
                }
            }
        }
    }
    stage.add(grid)
    count += 1
}

stage.render(svg, document)