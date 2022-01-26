import center from "./symbolsPosition/center";
import line from "./shapes/line";
import triangle from "./shapes/triangle";

/** draws asyncdrain channel */
export function asyncdrain(p5, startNode, endNode, arrowSize) {
  line(p5, startNode, endNode);

  center(p5, startNode, endNode, ["line", "line"]);

  triangle(p5, startNode, endNode, arrowSize, "start");
  triangle(p5, startNode, endNode, arrowSize, "end", "normal", true);
}
