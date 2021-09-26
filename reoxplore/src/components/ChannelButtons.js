import React from "react";
import * as channelsDisplay from "../pub";

export class ChannelButtons extends React.Component {
  getChannelNames() {
    let channelNames = [];
    let i = 0;
    for (let channel in channelsDisplay) {
      channelNames.push({ id: i, name: channel });
      i++;
    }
    return channelNames;
  }

  render() {
    const channels = this.getChannelNames();
    const buttons = channels.map((channel) => {
      return (
        <button
          key={channel.id}
          className={
            channel.name === this.props.channelMode
              ? "selected-button"
              : "not-selected-button"
          }
          onClick={(e) => {
            this.props.changeChannel(channel.name, e);
          }}
        >
          {channel.name}
        </button>
      );
    });

    return <div className="ChannelButtons">{buttons}</div>;
  }
}
