import center from "./symbolsPosition/center";
import line from "./shapes/line";
import triangle from "./shapes/triangle";

/** draws transform channel */
export function transform(p5, startNode, endNode, arrowSize) {
  line(p5, startNode, endNode);
  center(p5, startNode, endNode, ["triangle"], { isTriangleBig: true });
  triangle(p5, startNode, endNode, arrowSize);
}
