import React from "react";
import equal from "fast-deep-equal";
import * as channelsDisplay from "./channelsDisplay";

function getChannelNames() {
  let channelNames = [];
  for (let channel in channelsDisplay) {
    channelNames.push(channel);
  }
  return channelNames;
}

export class Treo extends React.Component {
  constructor(props) {
    super(props);
    this.state = { treo: "", isCorrect: true, nodesReference: {} };
    this.changeTreo = this.changeTreo.bind(this);
  }

  changeTreo(newTreo) {
    this.buildChannelsFromTreo(newTreo);
  }

  parseTreo(treo) {
    const channelNames = getChannelNames();
    let channels = [];
    let readyToDraw = true;

    const lines = treo
      .replace(/\n/g, "") // remove breaklines
      .replace(/\s/g, "") // remove whitespaces
      .split(";") // split by ;
      .slice(0, -1); // also remove the last element because it's empty

    for (let line of lines) {
      const regex = /[a-z]+\(\d+,\d+\)#\(\d+,\d+\)\(\d+,\d+\)/;
      // channelMode(startLabel,endLabel)#(startPosition.x, startPosition.y)(endPosition.x, endPosition.y)
      if (!line.match(regex)) {
        console.log(`fix ${line}`);
        readyToDraw = false;
        break;
      }
      const channelMode = line.match(/[a-z]+/)[0];
      if (!channelNames.includes(channelMode)) {
        console.log(`${channelMode} is not a valid channel`);
        readyToDraw = false;
        break;
      }

      const matchedNumbers = line.match(/\d+/g);
      channels.push({
        startNode: {
          x: Number(matchedNumbers[2]),
          y: Number(matchedNumbers[3]),
          label: Number(matchedNumbers[0]),
        },
        endNode: {
          x: Number(matchedNumbers[4]),
          y: Number(matchedNumbers[5]),
          label: Number(matchedNumbers[1]),
        },
        channelMode: channelMode,
      });
    }
    return {readyToDraw, channels};
  }

  getUpdatedChannels(oldChannels, newChannels) {
    function updateNodePosition(i, c, oneNode, otherNode, oneNodeLines) {
      // compares old and new treos and updates the oneNode's position if label changes
      // so nodes with the same label have the same position
      if (c[oneNode].label !== oldChannels[i][oneNode].label) {
        for (let line of oneNodeLines){ // lines where oneNode is referenced in treo
          if (line !== i) {
            let nodeBefore;
            if (c[oneNode].label === newChannels[line][oneNode].label)
              nodeBefore = newChannels[line][oneNode];
            else if (c[oneNode].label === newChannels[line][otherNode].label)
              nodeBefore = newChannels[line][otherNode];
            c[oneNode] = {...c[oneNode], x: nodeBefore.x, y: nodeBefore.y};
          }
        }
      }
    }
    let line = 0;
    for (let c of newChannels) {
      updateNodePosition(line, c, "endNode", "startNode", this.state.nodesReference[c.endNode.label]);
      updateNodePosition(line, c, "startNode", "endNode", this.state.nodesReference[c.startNode.label]);
      line++;
    }
    return newChannels;
  }

  buildChannelsFromTreo(newTreo) {
    const oldChannels = this.props.channels;
    let {readyToDraw, channels} = this.parseTreo(newTreo);

    channels = this.getUpdatedChannels(oldChannels, channels);

    if (readyToDraw) {
      this.setState({ isCorrect: true });
      this.props.updateDrawingBasedOnTreo(channels);
    } else {
      this.setState({ isCorrect: false });
    }
    this.setState({ treo: newTreo });
  }

  getTreoFromDrawing(startNode, endNode, channelMode) {
    // writes treo to update textarea value
    const nodes = `(${startNode.label}, ${endNode.label})`;
    const startPosition = `${Math.trunc(startNode.x)}, ${Math.trunc(
      startNode.y
    )}`;
    const endPosition = `${Math.trunc(endNode.x)}, ${Math.trunc(endNode.y)}`;
    const newTreo = `${channelMode}${nodes} # (${startPosition}) (${endPosition}); \n`;
    return newTreo;
  }

  addNodeReference(label, lineNumber) {
    // nodesReference indicates which lines this node was referenced in the treo
    let newNodesReference = this.state.nodesReference;
    if (!(label in this.state.nodesReference))
      newNodesReference[label] = new Set();
    newNodesReference[label].add(lineNumber);
    this.setState({ nodesReference: newNodesReference });
  }

  // componentDidUpdate is triggered when either the props or the state has changed
  // to not enter a loop, we need to verify if the props changed before updating again
  componentDidUpdate(prevProps) {
    if (!equal(this.props.channels, prevProps.channels)) {
      let newTreo = "";
      let lineNumber = 0;
      this.setState({ nodesReference: {} });
      for (let c of this.props.channels) {
        newTreo += this.getTreoFromDrawing(
          c.startNode,
          c.endNode,
          c.channelMode
        );
        this.addNodeReference(c.startNode.label, lineNumber);
        this.addNodeReference(c.endNode.label, lineNumber);
        lineNumber++;
      }
      this.setState({ treo: newTreo });
    }
  }

  render() {
    return (
      <div className="Treo">
        <textarea
          className={this.state.isCorrect ? "right" : "wrong"}
          cols="40"
          rows="10"
          value={this.state.treo}
          onChange={(e) => {
            this.changeTreo(e.target.value, e);
          }}
        />
      </div>
    );
  }
}
