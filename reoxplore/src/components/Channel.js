import * as channelsDisplay from "../pub";

class Channel {
  /**
   * @param p p5.js instance to create the drawing
   * @param startNode node where the channel starts from
   * @param endNode node where the channel ends
   * @param {string} channelMode the channel mode that determs the drawing type
   */
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
