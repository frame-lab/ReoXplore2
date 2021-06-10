import React from "react";
import { render } from "react-dom";
import P5Wrapper from "react-p5-wrapper";
import Node from "./components/Node";
import Channel from "./components/Channel";
import { ChannelButtons } from "./components/ChannelButtons";

class App extends React.Component {
  constructor() {
    super();

    this.state = { channel: "sync" };
    this.sketch = this.sketch.bind(this);
    this.changeChannel = this.changeChannel.bind(this);
  }

  sketch(p) {
    let count = 1;
    let previous_node;
    let first_node = true;
    let self = this; //to access this.changeChannel on function main

    let nodes = [];
    let channels = [];

    p.setup = () => {
      let canvas = p.createCanvas(800, 400);
      canvas.mouseClicked(main);
      p.textSize(12);
    };

    p.draw = () => {
      p.background(220);

      for (let i = 0; i < channels.length; i++) {
        channels[i].display();
      }

      for (let i = 0; i < nodes.length; i++) {
        nodes[i].display();
      }
    };

    function main() {
      let node;
      let node_clicked = false;
      let new_node_created = false;

      for (let i = 0; i < nodes.length; i++) {
        //checks if a node was clicked
        if (nodes[i].clicked(p.mouseX, p.mouseY)) {
          if (first_node) {
            previous_node = nodes[i];
          } else {
            node = nodes[i];
          }
          node_clicked = true;
        }
      }
      if (!node_clicked) {
        //create new node
        node = new Node(p, p.mouseX, p.mouseY, count);
        nodes.push(node);
        new_node_created = true;
      }

      if (!first_node) {
        if (!previous_node) {
          //if didnt click on a previous node, get the last one
          previous_node = nodes[count - 2];
        }
        if (previous_node !== node) {
          let channel = new Channel(p, previous_node, node, self.state.channel);
          channels.push(channel);
        }
        previous_node = null;
      }

      if (new_node_created) count++;
      first_node = !first_node;
    }
  }

  changeChannel(newMode) {
    this.setState({ channel: newMode });
  }

  render() {
    return (
      <div>
        <h3>Channels</h3>
        <ChannelButtons changeChannel={this.changeChannel} />
        <P5Wrapper sketch={this.sketch.bind(this)} />
      </div>
    );
  }
}

render(<App />, document.getElementById("root"));
