/** draws an ellipse in the middle of startNode and endNode */
export default function ellipse(p5, startNode, endNode, radius) {
  const mediumX = (startNode.x + endNode.x) / 2;
  const mediumY = (startNode.y + endNode.y) / 2;
  p5.ellipse(mediumX, mediumY, radius);
}
