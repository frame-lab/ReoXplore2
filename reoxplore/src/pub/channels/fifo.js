// function for drawing fifo channel

export function fifo(p5, startNode, endNode, arrowSize) {
  const angle = p5.atan2(startNode.y - endNode.y, startNode.x - endNode.x); //angle of the line
  const mediumX = (startNode.x + endNode.x) / 2;
  const mediumY = (startNode.y + endNode.y) / 2;

  const rectWidth = arrowSize;
  const rectHeight = arrowSize * 2;

  p5.push(); //start new drawing state
  p5.translate(mediumX, mediumY); //translates to middle of the line
  p5.rotate(angle - p5.HALF_PI); //rotates the rectangle
  p5.rect(-rectWidth / 2, -rectHeight / 2, rectWidth, rectHeight);
  p5.pop();

  p5.line(startNode.x, startNode.y, endNode.x, endNode.y);

  p5.push();
  p5.translate(endNode.x, endNode.y); //translates to the destination vertex
  p5.rotate(angle - p5.HALF_PI); //rotates the arrow point
  p5.triangle(
    -arrowSize / 2,
    arrowSize * 2,
    arrowSize / 2,
    arrowSize * 2,
    0,
    arrowSize
  ); //draws the arrow point as a triangle
  p5.pop();
}
