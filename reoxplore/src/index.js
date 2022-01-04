import React from "react";
import { render } from "react-dom";
import { ReactP5Wrapper } from "react-p5-wrapper";
import "./style.css";
import Node from "./components/Node";
import Channel from "./components/Channel";
import getUniqueNodesFromArray from "./utils/getUniqueNodesFromArray";
import validateCanvasSize from "./utils/validateCanvasSize";
import { ChannelButtons } from "./components/ChannelButtons";
import { Treo } from "./components/Treo";
import TreoToCustomLanguage from "./components/TreoToCustomLanguage";

class App extends React.Component {
  constructor() {
    super();

    this.state = {
      channel: "sync",
      nodes: [],
      channels: [],
      treoEntry: [],
      treoCode: "",
      canvasX: 800,
      canvasY: 400,
    };
    this.sketch = this.sketch.bind(this);
    this.changeChannel = this.changeChannel.bind(this);
    this.updateDrawingBasedOnTreo = this.updateDrawingBasedOnTreo.bind(this);
    this.saveTreoCode = this.saveTreoCode.bind(this);
  }

  sketch(p) {
    let count = 1;
    let previousNode;
    let firstNode = true;
    let designMode = false;
    const self = this; //to access this.state.channel on function main

    p.setup = () => {
      const canvas = p.createCanvas(this.state.canvasX, this.state.canvasY);
      canvas.mouseClicked(main);
      p.textSize(12);
    };

    p.keyTyped = () => {
      if (p.key === "d") designMode = true;
      else designMode = false;
    };

    p.mouseDragged = () => {
      const mouseInResizeArea =
        p.mouseX > this.state.canvasX - 25 &&
        p.mouseY > this.state.canvasY - 25 &&
        p.mouseX < this.state.canvasX + 25 &&
        p.mouseY < this.state.canvasY + 25;
      const isCanvasSizeValid = validateCanvasSize(p.mouseX, p.mouseY, this.state.nodes);
      if (mouseInResizeArea && isCanvasSizeValid) {
        p.resizeCanvas(p.mouseX, p.mouseY);
        this.setState({ canvasX: p.mouseX, canvasY: p.mouseY });
      }

      if (designMode) moveNode();
    };

    p.draw = () => {
      p.background(220);
      drawResizeCanvasIcon(self.state.canvasX, self.state.canvasY);
      if (designMode) drawDesignModeText();

      if (self.state.treoEntry.length > 0) {
        // add channels and nodes coming from treo
        addChannelsFromTreo(self.state.treoEntry);
      }

      for (const channel of self.state.channels) {
        channel.display();
      }

      for (const node of self.state.nodes) {
        node.display();
      }
    };

    function main() {
      if (designMode) return;
      let currentNode;
      let nodeClicked = false;
      let newNodeCreated = false;

      for (const node of self.state.nodes) {
        //checks if a node was clicked
        if (node.clicked(p.mouseX, p.mouseY)) {
          if (firstNode) {
            previousNode = node;
          } else {
            currentNode = node;
          }
          nodeClicked = true;
        }
      }
      if (!nodeClicked) {
        //create new node
        currentNode = new Node(p, p.mouseX, p.mouseY, count);
        self.setState({ nodes: self.state.nodes.concat(currentNode) });
        newNodeCreated = true;
        if (!previousNode) previousNode = currentNode;
      }

      if (!firstNode) {
        if (previousNode !== currentNode) {
          const channel = new Channel(p, previousNode, currentNode, self.state.channel);
          self.setState({ channels: self.state.channels.concat(channel) });
        }
        previousNode = null;
      }

      if (newNodeCreated) count++;
      firstNode = !firstNode;
    }

    function addChannelsFromTreo(treoEntry) {
      let newNodes = [];
      let newChannels = [];
      for (let treo of treoEntry) {
        const startNode = new Node(p, treo.startNode.x, treo.startNode.y, treo.startNode.label);
        const endNode = new Node(p, treo.endNode.x, treo.endNode.y, treo.endNode.label);
        newNodes.push(startNode, endNode);
        newChannels.push(new Channel(p, startNode, endNode, treo.channelMode));
      }
      const newUniqueNodes = getUniqueNodesFromArray(newNodes);
      self.setState({ treoEntry: [], nodes: newUniqueNodes, channels: newChannels });
    }

    function moveNode() {
      for (const node of self.state.nodes) {
        if (node.clicked(p.mouseX, p.mouseY)) {
          let nodesCollapsed = false;
          for (const otherNode of self.state.nodes) {
            if (node.label === otherNode.label) continue;
            if (otherNode.clicked(p.mouseX, p.mouseY)) nodesCollapsed = true;
          }
          if (!nodesCollapsed) {
            node.x = p.mouseX;
            node.y = p.mouseY;
            self.setState({ nodes: self.state.nodes });
          }
        }
      }
    }

    function drawResizeCanvasIcon(x, y) {
      p.push();
      p.stroke(100);
      for (let i = 4; i < 20; i += 4) p.line(x - 2, y - i, x - i, y - 2);
      p.pop();
    }

    function drawDesignModeText() {
      p.push();
      p.textSize(12);
      p.textFont("monospace");
      p.text("design mode", 10, 20);
      p.pop();
    }
  }

  changeChannel(newMode) {
    this.setState({ channel: newMode });
  }

  updateDrawingBasedOnTreo(channelsFromTreo) {
    this.setState({ treoEntry: channelsFromTreo });
  }

  saveTreoCode(treo) {
    this.setState({ treoCode: treo });
  }

  render() {
    return (
      <main>
        <h1>ReoXplore</h1>
        <section className="grid-container">
          <h3>Channels</h3>
          <ChannelButtons changeChannel={this.changeChannel} channelMode={this.state.channel} />
          <div className="p5container">
            <ReactP5Wrapper sketch={this.sketch} />
          </div>
          <Treo
            nodes={this.state.nodes}
            channels={this.state.channels}
            updateDrawingBasedOnTreo={this.updateDrawingBasedOnTreo}
            saveTreoCode={this.saveTreoCode}
          />
        </section>
        <section className="options">
          <h3>Options</h3>
          <TreoToCustomLanguage treo={this.state.treoCode} />
        </section>
      </main>
    );
  }
}

render(<App />, document.getElementById("root"));
