export function channelHasParameter(channel) {
  if (
    channel === "filter" ||
    channel === "transform" ||
    channel === "timer" ||
    channel === "timeddelay" ||
    channel === "timedtransformer"
  )
    return true;

  return false;
}

export function getChannelDefaultParameter(channel) {
  if (channel === "timer") return "[5, var - 1;]";
  if (channel === "timeddelay") return "[5, 10;]";
  if (channel === "timedtransformer") return "[5, var - 1;]";

  return "[,]";
}
