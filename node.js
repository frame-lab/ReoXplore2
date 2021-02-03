class Node {

    constructor(x, y, label) {
        this.x = x
        this.y = y
        this.label = label    
    }

    draw() {
        noStroke()
        fill(255)
        ellipse(this.x, this.y, 20, 20)
        fill(10)
        text(this.label, this.x - 5, this.y + 4)
    }
}