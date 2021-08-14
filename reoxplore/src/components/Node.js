class Node {
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
    if (d <= this.radius) {
      return true;
    }
  }
}

export default Node;
