/**
 * draws a line between startNode and endNode
 * @param {boolean} isDashed if true, draws a dashed line, otherwise draws a solid line
 */
export default function line(p5, startNode, endNode, isDashed) {
  if (isDashed) p5.drawingContext.setLineDash([5, 10]);
  p5.line(startNode.x, startNode.y, endNode.x, endNode.y);
  p5.drawingContext.setLineDash([]); //reset to solid line
}
