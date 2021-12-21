import triangle from "./shapes/triangle";
import line from "./shapes/line";
import center from "./symbolsPosition/center";

/** function for drawing timed delay channel */
export function timedtransform(p5, startNode, endNode, arrowSize) {
  line(p5, startNode, endNode);
  triangle(p5, startNode, endNode, arrowSize);
  center(p5, startNode, endNode, ["triangle", "circle"], { isTriangleBig: true });
}
