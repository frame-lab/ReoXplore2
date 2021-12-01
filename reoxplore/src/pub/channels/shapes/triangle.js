/** draws a triangle
 * @param {string} position "center" draws the triangle between startNode and endNode,
 * otherwise draws at endNode
 * @param {string} size "big" draws a big triangle, otherwise draws a normal triangle
 * @param {boolean} isInverted
 */
export default function triangle(
  p5,
  startNode,
  endNode,
  arrowSize,
  position,
  size,
  isInverted
) {
  const angle = p5.atan2(startNode.y - endNode.y, startNode.x - endNode.x); //angle of the line
  let point = { x: endNode.x, y: endNode.y };
  if (position === "start") {
    point = { x: startNode.x, y: startNode.y };
  } else if (position === "center") {
    point.x = (startNode.x + endNode.x) / 2;
    point.y = (startNode.y + endNode.y) / 2;
  }

  let rotationAngle = p5.HALF_PI;
  if (isInverted) rotationAngle *= -1;

  p5.push();
  p5.translate(point.x, point.y); //translates to the specific point
  p5.rotate(angle - rotationAngle); //rotates the arrow point

  if (isInverted || position === "start") p5.translate(0, -arrowSize * 4); // so the triangle is not exactly on top of node

  if (size === "big") {
    //draws the arrow point as a big triangle
    p5.triangle(-arrowSize, arrowSize, arrowSize, arrowSize, 0, -arrowSize / 2);
  } else {
    //draws the arrow point as a normal triangle
    p5.triangle(
      -arrowSize / 2,
      arrowSize * 2,
      arrowSize / 2,
      arrowSize * 2,
      0,
      arrowSize
    );
  }

  p5.pop();
}
