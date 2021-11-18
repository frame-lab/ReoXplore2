import React from "react";
import downloadIcon from "../assets/arrow.svg"

export default class DownloadButton extends React.Component {
  handleDownload = (fileData, fileName) => (e) => {
    e.preventDefault();
    const link = document.createElement("a");
    link.download = fileName;
    const blob = new Blob([fileData], { type: "text/plain" });
    link.href = URL.createObjectURL(blob);
    link.click();
    URL.revokeObjectURL(link.href);
  };

  render() {
    return (
      <button
        type="button"
        id="download-button"
        onClick={this.handleDownload(this.props.fileData, this.props.fileName)}
      >
        <span>Download</span>
        <img src={downloadIcon} alt="download icon" />
      </button>
    );
  }
}
