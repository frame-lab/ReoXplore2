let count = 1

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

    let node = new Node(mouseX, mouseY, count)
    nodes.push(node);

    if (count % 2 == 0) {
        let previous_node = nodes[count-2]
        let channel = new Channel(previous_node, node, channelMode)
        channels.push(channel)
    }

    count++;
}

function chooseChannel(mode) {
    //call by button in html
    channelMode = mode
  }