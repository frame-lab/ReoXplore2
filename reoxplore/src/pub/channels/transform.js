import line from "./shapes/line";
import triangle from "./shapes/triangle";

/** draws transform channel */
export function transform(p5, startNode, endNode, arrowSize) {
  line(p5, startNode, endNode);
  triangle(p5, startNode, endNode, arrowSize, "center", "big");
  triangle(p5, startNode, endNode, arrowSize);
}
