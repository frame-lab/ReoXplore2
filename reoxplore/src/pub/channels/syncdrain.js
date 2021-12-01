import line from "./shapes/line";
import triangle from "./shapes/triangle";

/** draws syncdrain channel */
export function syncdrain(p5, startNode, endNode, arrowSize) {
  line(p5, startNode, endNode);
  triangle(p5, startNode, endNode, arrowSize, "start");
  triangle(p5, startNode, endNode, arrowSize, "end", "normal", true);
}
