import * as channelsDisplay from "./channelsDisplay";

class Channel {
  constructor(p, startNode, endNode, channelMode) {
    this.p = p;
    this.startNode = startNode;
    this.endNode = endNode;
    this.channelMode = channelMode;
  }

  display() {
    this.p.stroke(160);
    this.p.strokeWeight(2);
    this.p.fill(160);

    const arrowSize = 10;

    channelsDisplay[this.channelMode](
      this.p,
      this.startNode,
      this.endNode,
      arrowSize
    );
  }
}

export default Channel;
