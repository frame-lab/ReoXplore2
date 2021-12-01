import line from "./shapes/line";
import triangle from "./shapes/triangle";

/** draws lossysync channel */
export function lossysync(p5, startNode, endNode, arrowSize) {
  line(p5, startNode, endNode, true);
  triangle(p5, startNode, endNode, arrowSize);
}
