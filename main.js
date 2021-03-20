let count = 1
let previous_node
let first_node = true
let channelMode

let nodes = []
let channels = []

function setup() {
    canvas = createCanvas(400, 400)
    canvas.mouseClicked(main)
    textSize(12)
}

function draw() {
    background(220)

    for (let i = 0; i < channels.length; i++) {
        channels[i].draw()
    }

    for (let i = 0; i < nodes.length; i++) {
        nodes[i].draw()
    }
}

function main() {
    let node
    let node_clicked = false
    let new_node_created = false

    for (let i = 0; i < nodes.length; i++) { //checks if a node was clicked
        if (nodes[i].clicked(mouseX, mouseY)){
            if (first_node) {
                previous_node = nodes[i]
            } else {
                node = nodes[i]
            }
            node_clicked = true
        }
    }
    if (!node_clicked) { //create new node
        node = new Node(mouseX, mouseY, count)
        nodes.push(node);
        new_node_created = true
    }

    if (!first_node) {
        if (!previous_node) { //if didnt click on a previous node, get the last one
            previous_node = nodes[count-2]
        }
        let channel = new Channel(previous_node, node, channelMode)
        channels.push(channel)
        previous_node = null
    }

    if (new_node_created) count++;
    first_node = !first_node
}

function chooseChannel(mode) {
    //call by button in html
    channelMode = mode
}

