/** Compare the X and Y positions of the canvas to all nodes and 
 * do not allow the canvas to be smaller than the position of any node.
 * @param {number} x canvas desired x position
 * @param {number} y canvas desired y position
 * @param {Array} nodes list of nodes
 * @returns {boolean} true if canvas desired width and height are valid;
 * false otherwise.
 */
export default function validateCanvasSize(x, y, nodes) {
  for (const node of nodes) {
    const minWidth = node.x + node.radius / 2;
    const minHeight = node.y + node.radius / 2;
    if (x <= minWidth || y <= minHeight) return false;
  }
  return true;
}
