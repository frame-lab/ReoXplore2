// function for drawing transform channel

export function transform(p5, startNode, endNode, arrowSize) {
  const angle = p5.atan2(startNode.y - endNode.y, startNode.x - endNode.x); //angle of the line
  const mediumX = (startNode.x + endNode.x) / 2;
  const mediumY = (startNode.y + endNode.y) / 2;

  p5.push();
  p5.translate(mediumX, mediumY); // translate the arrow to the center
  p5.rotate(angle - p5.HALF_PI); //rotates the arrow point
  p5.triangle(-arrowSize, arrowSize, arrowSize, arrowSize, 0, -arrowSize / 2); //draws the arrow point as a big triangle
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
