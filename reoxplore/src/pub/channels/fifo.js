import center from "./symbolsPosition/center";
import line from "./shapes/line";
import triangle from "./shapes/triangle";

/** draws fifo channel */
export function fifo(p5, startNode, endNode, arrowSize) {
  line(p5, startNode, endNode);
  center(p5, startNode, endNode, ["rectangle"]);
  triangle(p5, startNode, endNode, arrowSize);
}
