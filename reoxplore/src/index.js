import React from "react";
import { render } from "react-dom";
import P5Wrapper from "react-p5-wrapper";
import "./style.css";
import Node from "./components/Node";
import Channel from "./components/Channel";
import getUniqueNodesFromArray from "./utils/getUniqueNodesFromArray";
import { ChannelButtons } from "./components/ChannelButtons";
import { Treo } from "./components/Treo";
import TreoToCustomLanguage from "./components/TreoToCustomLanguage";
class App extends React.Component {
  constructor() {
    super();

    this.state = { channel: "sync", nodes: [], channels: [], treoEntry: [], treoCode: "" };
    this.sketch = this.sketch.bind(this);
    this.changeChannel = this.changeChannel.bind(this);
    this.updateDrawingBasedOnTreo = this.updateDrawingBasedOnTreo.bind(this);
    this.saveTreoCode = this.saveTreoCode.bind(this);
  }

  sketch(p) {
    let count = 1;
    let previous_node;
    let first_node = true;
    const self = this; //to access this.state.channel on function main

    p.setup = () => {
      const canvas = p.createCanvas(800, 400);
      canvas.mouseClicked(main);
      p.textSize(12);
    };

    p.draw = () => {
      p.background(220);

      if (self.state.treoEntry.length > 0) {
        // add channels and nodes coming from treo
        addChannelsFromTreo(self.state.treoEntry);
      }

      for (let i = 0; i < self.state.channels.length; i++) {
        self.state.channels[i].display();
      }

      for (let i = 0; i < self.state.nodes.length; i++) {
        self.state.nodes[i].display();
      }
    };

    function main() {
      let node;
      let node_clicked = false;
      let new_node_created = false;

      for (let i = 0; i < self.state.nodes.length; i++) {
        //checks if a node was clicked
        if (self.state.nodes[i].clicked(p.mouseX, p.mouseY)) {
          if (first_node) {
            previous_node = self.state.nodes[i];
          } else {
            node = self.state.nodes[i];
          }
          node_clicked = true;
        }
      }
      if (!node_clicked) {
        //create new node
        node = new Node(p, p.mouseX, p.mouseY, count);
        self.setState({ nodes: self.state.nodes.concat(node) });
        new_node_created = true;
        if (!previous_node) previous_node = node;
      }

      if (!first_node) {
        if (previous_node !== node) {
          const channel = new Channel(p, previous_node, node, self.state.channel);
          self.setState({ channels: self.state.channels.concat(channel) });
        }
        previous_node = null;
      }

      if (new_node_created) count++;
      first_node = !first_node;
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
          <ChannelButtons
            changeChannel={this.changeChannel}
            channelMode={this.state.channel}
          />
          <div className="p5container">
            <P5Wrapper sketch={this.sketch.bind(this)} />
          </div>
          <h3 className="treo-title">Treo</h3>
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
