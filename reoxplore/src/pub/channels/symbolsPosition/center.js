
/** draws a symbol in the middle of startNode and endNode
 * @param {string[]} symbols symbols to draw: "circle" or "rectangle"
 * @param {object} options object with drawing options
 * @param {number?} options.radius size of the circle, default is 10
 * @param {boolean?} options.isDouble if true, draws two symbols, otherwise draws only one; default is false
 */
export default function center(p5, startNode, endNode, symbols, options) {
  const centerX = (startNode.x + endNode.x) / 2;
  const centerY = (startNode.y + endNode.y) / 2;
  const centerPoint = { x: centerX, y: centerY };
  const angle = p5.atan2(startNode.y - endNode.y, startNode.x - endNode.x); //angle of the line

  p5.push();
  p5.translate(centerPoint.x, centerPoint.y); // translate to the middle of startNode and endNode
  p5.rotate(angle - p5.HALF_PI); // rotates to the same inclination of the lines
  if (symbols.length > 1) {
    centerTwoSymbols(p5, symbols[0], symbols[1], options);
  } else {
    drawSymbol(p5, symbols[0], options);
  }
  p5.pop();
}

function centerTwoSymbols(p5, symbol1, symbol2, options) {
  const distanceFromCenter = 8;
 
  // first symbol
  p5.push();
  p5.translate(0, distanceFromCenter);
  drawSymbol(p5, symbol1, options);
  p5.pop();

  // second symbol
  p5.push();
  p5.translate(0, -distanceFromCenter);
  drawSymbol(p5, symbol2, options);
  p5.pop();
}

function drawSymbol(p5, symbol, options) {
  const size = options?.size ?? 10;
  if (symbol === "circle") {
    p5.ellipse(0, 0, size);
  } else if (symbol === "rectangle") {
    const rectWidth = size;
    const rectHeight = size * 2;
    p5.rect(-rectWidth / 2, -rectHeight / 2, rectWidth, rectHeight);
  } else if (symbol === "triangle") {
    if (options?.isTriangleBig) {
      //draws the arrow point as a big triangle
      p5.triangle(-size, size, size, size, 0, -size / 2);
    } else {
      //draws the arrow point as a normal triangle
      p5.triangle(-size / 2, size * 2, size / 2, size * 2, 0, size);
    }
  }
}
