// Functions for drawing the channels

export function sync(p5, startNode, endNode, arrowSize) {
  let angle = p5.atan2(startNode.y - endNode.y, startNode.x - endNode.x); //angle of the line

  p5.line(startNode.x, startNode.y, endNode.x, endNode.y);

  p5.push();
  p5.translate(endNode.x, endNode.y); //translates to the destination vertex
  p5.rotate(angle - p5.HALF_PI);
  p5.triangle(
    -arrowSize / 2,
    arrowSize * 2,
    arrowSize / 2,
    arrowSize * 2,
    0,
    arrowSize
  ); //draws the arrow point as a triangle
  p5.pop();
}

export function lossy_sync(p5, startNode, endNode, arrowSize) {
  let angle = p5.atan2(startNode.y - endNode.y, startNode.x - endNode.x); //angle of the line

  p5.drawingContext.setLineDash([5, 10]);
  p5.line(startNode.x, startNode.y, endNode.x, endNode.y);
  p5.drawingContext.setLineDash([]); //reset to solid line

  p5.push();
  p5.translate(endNode.x, endNode.y); //translates to the destination vertex
  p5.rotate(angle - p5.HALF_PI);
  p5.triangle(
    -arrowSize / 2,
    arrowSize * 2,
    arrowSize / 2,
    arrowSize * 2,
    0,
    arrowSize
  ); //draws the arrow point as a triangle
  p5.pop();
}

export function fifo(p5, startNode, endNode, arrowSize) {
  let angle = p5.atan2(startNode.y - endNode.y, startNode.x - endNode.x); //angle of the line
  let mediumX = (startNode.x + endNode.x) / 2;
  let mediumY = (startNode.y + endNode.y) / 2;

  let rectWidth = arrowSize;
  let rectHeight = arrowSize * 2;

  p5.push(); //start new drawing state
  p5.translate(mediumX, mediumY); //translates to middle of the line
  p5.rotate(angle - p5.HALF_PI); //rotates the rectangle
  p5.rect(-rectWidth / 2, -rectHeight / 2, rectWidth, rectHeight);
  p5.pop();

  p5.line(startNode.x, startNode.y, endNode.x, endNode.y);

  p5.push();
  p5.translate(endNode.x, endNode.y); //translates to the destination vertex
  p5.rotate(angle - p5.HALF_PI);
  p5.triangle(
    -arrowSize / 2,
    arrowSize * 2,
    arrowSize / 2,
    arrowSize * 2,
    0,
    arrowSize
  ); //draws the arrow point as a triangle
  p5.pop();
}

export function transform(p5, startNode, endNode, arrowSize) {
  let angle = p5.atan2(startNode.y - endNode.y, startNode.x - endNode.x); //angle of the line
  let mediumX = (startNode.x + endNode.x) / 2;
  let mediumY = (startNode.y + endNode.y) / 2;

  p5.push();
  p5.translate(mediumX, mediumY);
  p5.rotate(angle - p5.HALF_PI);
  p5.triangle(-arrowSize, arrowSize, arrowSize, arrowSize, 0, -arrowSize / 2); //draws the arrow point as a big triangle
  p5.pop();

  p5.line(startNode.x, startNode.y, endNode.x, endNode.y);

  p5.push();
  p5.translate(endNode.x, endNode.y); //translates to the destination vertex
  p5.rotate(angle - p5.HALF_PI);
  p5.triangle(
    -arrowSize / 2,
    arrowSize * 2,
    arrowSize / 2,
    arrowSize * 2,
    0,
    arrowSize
  ); //draws the arrow point as a triangle
  p5.pop();
}

export function sync_drain(p5, startNode, endNode, arrowSize) {
  let angle = p5.atan2(startNode.y - endNode.y, startNode.x - endNode.x); //angle of the line

  p5.line(startNode.x, startNode.y, endNode.x, endNode.y);

  p5.push();
  p5.translate(startNode.x, startNode.y); //translates to the initial vertex
  p5.rotate(angle - p5.HALF_PI);
  p5.triangle(
    -arrowSize / 2,
    -arrowSize * 1.8,
    arrowSize / 2,
    -arrowSize * 1.8,
    0,
    -arrowSize * 3
  ); //draws the arrow point as a triangle
  p5.pop();

  p5.push();
  p5.translate(endNode.x, endNode.y); //translates to the destination vertex
  p5.rotate(angle + p5.HALF_PI);
  p5.triangle(
    -arrowSize / 2,
    -arrowSize * 1.8,
    arrowSize / 2,
    -arrowSize * 1.8,
    0,
    -arrowSize * 3
  ); //draws the arrow point as a triangle
  p5.pop();
}

export function async_drain(p5, startNode, endNode, arrowSize) {
  let angle = p5.atan2(startNode.y - endNode.y, startNode.x - endNode.x); //angle of the line
  let mediumX = (startNode.x + endNode.x) / 2;
  let mediumY = (startNode.y + endNode.y) / 2;

  p5.line(startNode.x, startNode.y, endNode.x, endNode.y);

  p5.push();
  p5.translate(mediumX, mediumY);
  p5.rotate(angle);
  p5.line(-4, arrowSize, -4, -arrowSize);
  p5.line(4, arrowSize, 4, -arrowSize);
  p5.pop();

  p5.push();
  p5.translate(startNode.x, startNode.y); //translates to the initial vertex
  p5.rotate(angle - p5.HALF_PI);
  p5.triangle(
    -arrowSize / 2,
    -arrowSize * 1.8,
    arrowSize / 2,
    -arrowSize * 1.8,
    0,
    -arrowSize * 3
  ); //draws the arrow point as a triangle
  p5.pop();

  p5.push();
  p5.translate(endNode.x, endNode.y); //translates to the destination vertex
  p5.rotate(angle + p5.HALF_PI);
  p5.triangle(
    -arrowSize / 2,
    -arrowSize * 1.8,
    arrowSize / 2,
    -arrowSize * 1.8,
    0,
    -arrowSize * 3
  ); //draws the arrow point as a triangle
  p5.pop();
}

// If you want to add a new type of channel, you just need to add a new function here:
// export function new_channel_name(p5, startNode, endNode, arrowSize) {
  // write your p5js code here
  // you can try it out in the p5 editor first: https://editor.p5js.org/
  // but when passing the code here, remember that all p5js functions need to have a `p5.` before it
    // example: `line(10,20, 10, 100);` in p5 editor must be `p5.line(10,20, 10, 100);` here
// }

