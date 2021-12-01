import line from "./shapes/line";
import triangle from "./shapes/triangle";

/** draws asyncdrain channel */
export function asyncdrain(p5, startNode, endNode, arrowSize) {
  const angle = p5.atan2(startNode.y - endNode.y, startNode.x - endNode.x); //angle of the line
  const mediumX = (startNode.x + endNode.x) / 2;
  const mediumY = (startNode.y + endNode.y) / 2;

  line(p5, startNode, endNode);

  p5.push();
  p5.translate(mediumX, mediumY);
  p5.rotate(angle); //rotates the lines in the center
  p5.line(-4, arrowSize, -4, -arrowSize);
  p5.line(4, arrowSize, 4, -arrowSize);
  p5.pop();

  triangle(p5, startNode, endNode, arrowSize, "start");
  triangle(p5, startNode, endNode, arrowSize, "end", "normal", true);
}
