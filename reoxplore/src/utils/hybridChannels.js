export function isHybridChannel(channel) {
  if (channel === "timer") return true;
  if (channel === "timeddelay") return true;
  if (channel === "timedtransform") return true;

  return false;
}

export function getHybridDefaultParameters(channel) {
  if (channel === "timer") return "[5, var - 1;]";
  if (channel === "timeddelay") return "[5, 10;]";
  if (channel === "timedtransform") return "[5, var - 1;]";

  return "[,]"
}
