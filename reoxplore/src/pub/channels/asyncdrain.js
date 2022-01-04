import center from "./symbolsPosition/center";
import line from "./shapes/line";
import triangle from "./shapes/triangle";

/** draws asyncdrain channel */
export function asyncdrain(p5, startNode, endNode, arrowSize) {
  const angle = p5.atan2(startNode.y - endNode.y, startNode.x - endNode.x); //angle of the line
  const mediumX = (startNode.x + endNode.x) / 2;
  const mediumY = (startNode.y + endNode.y) / 2;

  line(p5, startNode, endNode);

  center(p5, startNode, endNode, ["line", "line"]);

  triangle(p5, startNode, endNode, arrowSize, "start");
  triangle(p5, startNode, endNode, arrowSize, "end", "normal", true);
}
