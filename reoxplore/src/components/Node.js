class Node {
  /**
   * @param p p5.js instance to create the drawing
   * @param {number} x node's x position
   * @param {number} y node's y position
   * @param {string} label node's label for identification
   */
  constructor(p, x, y, label) {
    this.p = p;
    this.x = x;
    this.y = y;
    this.label = label;
    this.radius = 20;
  }

  display() {
    this.p.noStroke();
    this.p.fill(255);
    this.p.ellipse(this.x, this.y, this.radius, this.radius);
    this.p.fill(10);
    this.p.text(this.label, this.x - 5, this.y + 4);
  }

  clicked(px, py) {
    const d = this.p.dist(px, py, this.x, this.y);
    return d <= this.radius;
  }
}

export default Node;
