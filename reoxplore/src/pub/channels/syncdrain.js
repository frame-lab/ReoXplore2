// function for drawing syncdrain channel

export function syncdrain(p5, startNode, endNode, arrowSize) {
  const angle = p5.atan2(startNode.y - endNode.y, startNode.x - endNode.x); //angle of the line

  p5.line(startNode.x, startNode.y, endNode.x, endNode.y);

  p5.push();
  p5.translate(startNode.x, startNode.y); //translates to the initial vertex
  p5.rotate(angle - p5.HALF_PI); //rotates the arrow point
  p5.triangle(
    -arrowSize / 2,
    -arrowSize * 1.8,
    arrowSize / 2,
    -arrowSize * 1.8,
    0,
    -arrowSize * 3
  ); //draws the arrow point as a triangle
  p5.pop();

  p5.push();
  p5.translate(endNode.x, endNode.y); //translates to the destination vertex
  p5.rotate(angle + p5.HALF_PI); //rotates the arrow point
  p5.triangle(
    -arrowSize / 2,
    -arrowSize * 1.8,
    arrowSize / 2,
    -arrowSize * 1.8,
    0,
    -arrowSize * 3
  ); //draws the arrow point as a triangle
  p5.pop();
}
