// function for drawing sync channel

export function sync(p5, startNode, endNode, arrowSize) {
  const angle = p5.atan2(startNode.y - endNode.y, startNode.x - endNode.x); //angle of the line

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
