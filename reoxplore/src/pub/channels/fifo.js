import line from "./shapes/line";
import rectangle from "./shapes/rectangle";
import triangle from "./shapes/triangle";

/** draws fifo channel */
export function fifo(p5, startNode, endNode, arrowSize) {
  line(p5, startNode, endNode);
  rectangle(p5, startNode, endNode, arrowSize);
  triangle(p5, startNode, endNode, arrowSize);
}
