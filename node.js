class Node {

    constructor(x, y, label) {
        this.x = x
        this.y = y
        this.label = label
        this.radius = 20
    }

    draw() {
        noStroke()
        fill(255)
        ellipse(this.x, this.y, this.radius, this.radius)
        fill(10)
        text(this.label, this.x - 5, this.y + 4)
    }

    clicked(px, py) {
        let d = dist(px, py, this.x, this.y)
        if (d <= this.radius ) {
            return true
        }
    }
}

