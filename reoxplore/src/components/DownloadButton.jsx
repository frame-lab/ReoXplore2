import React from "react";

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
        onClick={this.handleDownload(this.props.fileData, this.props.fileName)}
      >
        download
      </button>
    );
  }
}
