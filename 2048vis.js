let gridProps = {
    grid_location: {x: 75, y: 75},
    cell_size:{
        x_size: 75,
        y_size: 75
    },
    grid_dimensions:{
        x_size: 3,
        y_size: 3
    }
}

let grid = new Grid(gridProps)

for (let c = 0; c < 3; c++) {
    for (let r = 0; r < 3; r++) {
        let tuples = Board.squares.tuples()
        for (t of tuples){
            atoms = t.atoms()
            if (atoms[0].id() == c && atoms[1].id() == r) {
                let v = atoms[2].join(cell).tuples()[0]
                if (v != undefined) {
                    let squareProps = {
                        coords: {x: 100, y:100},
                        height: 60,
                        width: 60,
                        color: "#fddeb3",
                        label: v.join(value).tuples()[0].atoms()[0].id().toString()
                    };
                    let square = new Rectangle(squareProps)
                    grid.add({x: c, y: r}, square)
                }
            }
        }
    }
}

stage = new Stage()
stage.add(grid)
stage.render(svg, document)