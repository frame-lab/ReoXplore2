import center from "./symbolsPosition/center";
import line from "./shapes/line";
import triangle from "./shapes/triangle";

/** draws fifo channel 
 * fifo1 it stores exactly one data in the buffer
*/
export function fifo1(p5, startNode, endNode, arrowSize) {
  line(p5, startNode, endNode);
  center(p5, startNode, endNode, ["rectangle"]);
  triangle(p5, startNode, endNode, arrowSize);
}
