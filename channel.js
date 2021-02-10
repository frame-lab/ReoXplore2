class Channel {

    constructor(startNode, endNode, channelMode) {
        this.startNode = startNode
        this.endNode = endNode
        this.channelMode = channelMode
    }

    draw() {
        stroke(160)
        strokeWeight(2)
        fill(160)

        let arrowSize = 10
        let angle = atan2(this.startNode.y - this.endNode.y, this.startNode.x - this.endNode.x) //angle of the line
        let mediumX = (this.startNode.x + this.endNode.x) / 2
        let mediumY = (this.startNode.y + this.endNode.y) / 2


        switch (this.channelMode) {
            case 'lossy_sync':
                drawingContext.setLineDash([5, 10])
                break

            case 'fifo':
                let rectWidth = arrowSize
                let rectHeight = arrowSize * 2

                push() //start new drawing state
                translate(mediumX, mediumY) //translates to middle of the line
                rotate(angle - HALF_PI) //rotates the rectangle
                rect(-rectWidth / 2, -rectHeight / 2, rectWidth, rectHeight)
                pop()
                break

            case 'transform':
                push()
                translate(mediumX, mediumY)
                rotate(angle - HALF_PI)
                triangle(-arrowSize, arrowSize, arrowSize, arrowSize, 0, -arrowSize / 2) //draws the arrow point as a big triangle
                pop()
                break

            case 'async_drain':
                push()
                translate(mediumX, mediumY)
                rotate(angle)
                line(-4, arrowSize, -4, -arrowSize)
                line(4, arrowSize, 4, -arrowSize)
                pop()
                //dont use break here because asnyc_drain also has sync_drain's arrows
            case 'sync_drain':
                push()
                translate(this.startNode.x, this.startNode.y) //translates to the initial vertex
                rotate(angle - HALF_PI)
                triangle(-arrowSize / 2, -arrowSize * 1.8, arrowSize / 2, -arrowSize * 1.8, 0, -arrowSize * 3) //draws the arrow point as a triangle
                pop()
                push()
                translate(this.endNode.x, this.endNode.y) //translates to the destination vertex
                rotate(angle + HALF_PI)
                triangle(-arrowSize / 2, -arrowSize * 1.8, arrowSize / 2, -arrowSize * 1.8, 0, -arrowSize * 3) //draws the arrow point as a triangle
                pop()
        }

        line(this.startNode.x, this.startNode.y, this.endNode.x, this.endNode.y)
        drawingContext.setLineDash([]) //reset to solid line

        if (!['sync_drain', 'async_drain'].includes(this.channelMode)) {
            // this code is to make the arrow point:
            push()
            translate(this.endNode.x, this.endNode.y) //translates to the destination vertex
            rotate(angle - HALF_PI)
            triangle(-arrowSize / 2, arrowSize * 2, arrowSize / 2, arrowSize * 2, 0, arrowSize) //draws the arrow point as a triangle
            pop()
        }
    }
}