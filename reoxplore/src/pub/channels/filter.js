import center from "./symbolsPosition/center";
import line from "./shapes/line";
import triangle from "./shapes/triangle";

/** draws filter channel */
export function filter(p5, startNode, endNode, arrowSize) {
  line(p5, startNode, endNode);
  center(p5, startNode, endNode, ["zigzag"]);
  triangle(p5, startNode, endNode, arrowSize);
}
