import triangle from "./shapes/triangle";
import line from "./shapes/line";

/** draws sync channel */ 
export function sync(p5, startNode, endNode, arrowSize) {
  line(p5, startNode, endNode);
  triangle(p5, startNode, endNode, arrowSize);
}
