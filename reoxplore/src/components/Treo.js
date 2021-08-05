import React from "react";
import equal from "fast-deep-equal";

export class Treo extends React.Component {
  constructor(props) {
    super(props);
    this.state = { treo: "" };
    this.changeTreo = this.changeTreo.bind(this);
  }

  changeTreo(newTreo) {
    this.setState({ treo: newTreo });
    this.buildChannelsFromTreo(newTreo);
  }

  buildChannelsFromTreo(newTreo) {
    let channels = [];
    let readyToDraw = true;

    let lines = newTreo
      .replace(/\n/g, "") // remove breaklines
      .replace(/\s/g, "") // remove whitespaces
      .split(";") // split by ;
      .slice(0, -1); // also remove the last element because it's empty

    for (let line of lines) {
      let splitedLine = line.split("(");
      let channelMode = splitedLine[0];
      let splitedLabel = splitedLine[1].replace(/\)|#/g, "").split(",");
      let startPosition = splitedLine[2].replace(/\)/g, "").split(",");
      let endPosition = splitedLine[3].replace(/\)/g, "").split(",");
      let startLabel = splitedLabel[0];
      let endLabel = splitedLabel[1];

      if (startLabel === "" || endLabel === "") {
        // TODO: create other conditions if other things are wrong
        readyToDraw = false;
        break;
      }

      channels.push({
        startNode: {
          x: Number(startPosition[0]),
          y: Number(startPosition[1]),
          label: Number(startLabel),
        },
        endNode: {
          x: Number(endPosition[0]),
          y: Number(endPosition[1]),
          label: Number(endLabel),
        },
        channelMode: channelMode,
      });
    }
    if (readyToDraw) this.props.updateDrawingBasedOnTreo(channels);
  }

  getTreoFromDrawing(startNode, endNode, channelMode) {
    // writes treo to update textarea value
    let nodes = `(${startNode.label}, ${endNode.label})`;
    let startPosition = `${Math.trunc(startNode.x)}, ${Math.trunc(
      startNode.y
    )}`;
    let endPosition = `${Math.trunc(endNode.x)}, ${Math.trunc(endNode.y)}`;
    let newTreo = `${channelMode}${nodes} # (${startPosition}) (${endPosition}); \n`;
    return newTreo;
  }

  // componentDidUpdate is triggered when either the props or the state has changed
  // to not enter a loop, we need to verify if the props changed before updating again
  componentDidUpdate(prevProps) {
    if (!equal(this.props.channels, prevProps.channels)) {
      let newTreo = "";
      for (let c of this.props.channels) {
        newTreo += this.getTreoFromDrawing(
          c.startNode,
          c.endNode,
          c.channelMode
        );
      }
      this.setState({ treo: newTreo });
    }
  }

  render() {
    return (
      <div className="Treo">
        <textarea
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
