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
  }

  updatesTreoWhileDrawing(startNode, endNode, channelMode) {
    // writes treo to update textarea value
    let nodes = `(${startNode.label}, ${endNode.label})`;
    let startPosition = `${Math.trunc(startNode.x)}, ${Math.trunc(startNode.y)}`;
    let endPosition = `${Math.trunc(endNode.x)}, ${Math.trunc(endNode.y)}`;
    let newTreo = `${channelMode}${nodes} # (${startPosition}), (${endPosition}); \n`;
    this.setState({ treo: this.state.treo.concat(newTreo) });
  }

  // componentDidUpdate is triggered when either the props or the state has changed
  // to not enter a loop, we need to verify if the props changed before updating again
  componentDidUpdate(prevProps) {
    if (!equal(this.props.channels, prevProps.channels)) {
      for (let c of this.props.channels) {
        this.updatesTreoWhileDrawing(c.startNode, c.endNode, c.channelMode);
      }
    }
  }

  render() {
    return (
      <div>
        <h3>Treo</h3>
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
