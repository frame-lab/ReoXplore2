import React from "react";
import equal from "fast-deep-equal";
import DownloadButton from "./DownloadButton";
import * as channelsDisplay from "../pub";
import { isHybridChannel, getHybridDefaultParameters } from "../utils/hybridChannels";

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
    let nodes = {};
    let channels = [];
    let readyToDraw = true;

    const lines = treo
      .split(/;\n/)
      .slice(0, -1); // remove the last element because it's empty

    for (let line of lines) {
      line = line.replace(/\s/g, "") // remove whitespaces
      const commentRegex = /#.*/;
      if (line.match(commentRegex)) {
        const nodeCommentRegex = /#\d+\(\d+,\d+\)/; // #nodeLabel(node.x,node.y)
        if (line.match(nodeCommentRegex)) {
          const nodeLabel = line.match(/#\d+/)[0].replace("#", "");
          const nodeX = line.match(/\(\d+/)[0].replace("(", "");
          const nodeY = line.match(/,\d+/)[0].replace(",", "");
          nodes[nodeLabel] = { x: Number(nodeX), y: Number(nodeY) };
          continue;
        } else {
          console.log(`fix ${line}`);
          readyToDraw = false;
          break;
        }
      }

      const regex = /[a-z]+\(\d+,\d+\)/; // channelMode(startLabel,endLabel)

      const hybridRegex = /[a-z]+\(\d+,\d+\)\[.*,.*\]/; // channelMode(startLabel,endLabel)[*,*]

      if (!line.match(regex) && !line.match(hybridRegex)) {
        console.error(`fix ${line}`);
        readyToDraw = false;
        break;
      }
      const channelMode = line.match(/[a-z]+/)[0];
      if (!channelNames.includes(channelMode)) {
        console.error(`${channelMode} is not a valid channel`);
        readyToDraw = false;
        break;
      }

      const labels = line.match(/\(\d+,\d+\)/)[0];
      const matchedNumbers = labels.match(/\d+/g);
      const startNodeLabel = Number(matchedNumbers[0]);
      const endNodeLabel = Number(matchedNumbers[1]);
      if (!(startNodeLabel in nodes) || !(endNodeLabel in nodes)) {
        console.log(`fix nodes positions`);
        readyToDraw = false;
        break;
      }
      channels.push({
        startNode: {
          x: nodes[startNodeLabel].x,
          y: nodes[startNodeLabel].y,
          label: startNodeLabel,
        },
        endNode: {
          x: nodes[endNodeLabel].x,
          y: nodes[endNodeLabel].y,
          label: endNodeLabel,
        },
        channelMode: channelMode,
      });
    }
    return { readyToDraw, channels };
  }

  buildChannelsFromTreo(newTreo) {
    let { readyToDraw, channels } = this.parseTreo(newTreo);

    if (readyToDraw) {
      this.setState({ isCorrect: true });
      this.props.updateDrawingBasedOnTreo(channels);
    } else {
      this.setState({ isCorrect: false });
    }
    this.setState({ treo: newTreo });
  }

  getTreoFromDrawing(startNode, endNode, channelMode) {
    /**
     * Get Treo of a drawing's channel to update textarea value
     * @param startNode the first Node object of the channel
     * @param endNode the second Node object of the channel
     * @param channelMode the channel mode
     * @returns a string with this channel treo
     */
    let treo;
    const nodes = `(${startNode.label},${endNode.label})`;
    if (isHybridChannel(channelMode)) {
      const parameters = getHybridDefaultParameters(channelMode);
      treo = `${channelMode}${nodes}${parameters};\n`;
    }
    else treo = `${channelMode}${nodes};\n`;

    return treo;
  }

  getNodesPositionsFromDrawing(nodes) {
    /**
     * Get the positions of the drawing's nodes to show in the Treo textarea as comments
     * @param nodes list of Nodes objects
     * @returns a string with all the nodes labels and theirs positions
     */
    let nodesPositions = "";
    for (let n of nodes) {
      const x = Math.trunc(n.x);
      const y = Math.trunc(n.y);
      nodesPositions += `# ${n.label} (${x}, ${y});\n`;
    }
    return nodesPositions + "\n";
  }

  // componentDidUpdate is triggered when either the props or the state has changed
  // to not enter a loop, we need to verify if the props changed before updating again
  componentDidUpdate(prevProps) {
    if (!equal(this.props.channels, prevProps.channels)) {
      let nodesPositions = this.getNodesPositionsFromDrawing(this.props.nodes);
      let newTreo = "";
      for (let c of this.props.channels) {
        newTreo += this.getTreoFromDrawing(
          c.startNode,
          c.endNode,
          c.channelMode
        );
      }
      this.props.saveTreoCode(newTreo);
      const treoWithComments = nodesPositions + newTreo;
      this.setState({ treo: treoWithComments });
    }
  }

  render() {
    return (
      <div className="Treo">
        <header>
          <h3 className="treo-title">Treo</h3>
          <DownloadButton fileData={this.state.treo} fileName="treo.txt" />
        </header>
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
