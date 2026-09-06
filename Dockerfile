FROM node:20-alpine

# font-dejavu is not decoration. The Shorts renderer burns a hook line and a
# call to action into the frame with ffmpeg's drawtext, and drawtext fails
# outright with "Cannot find a valid font" on an image that has none — which
# node:20-alpine does not. fontconfig comes with it so ffmpeg can resolve the
# family as well as the file.
#
# The server scans for the font at startup and reports what it found on
# /health, so if this package ever moves the failure is visible there rather
# than in a render at 2am.
RUN apk add --no-cache ffmpeg font-dejavu fontconfig

WORKDIR /app

COPY package.json ./
RUN npm install --omit=dev

COPY server.js ./

ENV DATA_DIR=/data
ENV PORT=8080
EXPOSE 8080

CMD ["node", "server.js"]
