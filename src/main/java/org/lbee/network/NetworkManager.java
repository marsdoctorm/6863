package org.lbee.network;

import org.lbee.protocol.Message;

import java.io.*;
import java.net.Socket;

public class NetworkManager {
    private final static int INTERVAL_BETWEEN_MESSAGE_POLL = 5;

    private final InputStream inputStream;
    private final PrintWriter writer;

    public NetworkManager(Socket socket) throws IOException {
        this.inputStream = socket.getInputStream();
        OutputStream outputStream = socket.getOutputStream();
        this.writer = new PrintWriter(outputStream, true);
    }

    public boolean send(Message message) throws IOException {
        writer.println("s:" + message.toString());
        BufferedReader reader = new BufferedReader(new InputStreamReader(this.inputStream));
        String data = reader.readLine();
        return !data.equals("null");
    }

    public Message receive(String processName, int timeout) throws IOException, TimeOutException {
        long lastSendTime = System.currentTimeMillis();
        while (true) {
            writer.println("r:" + processName);
            BufferedReader reader = new BufferedReader(new InputStreamReader(this.inputStream));
            String data = reader.readLine();

            if (!data.equals("null")) {
                String[] components = data.split(";");
                return new Message(components);
            }

            try {
                Thread.sleep(INTERVAL_BETWEEN_MESSAGE_POLL);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }

            long elapsedTime = System.currentTimeMillis() - lastSendTime;
            if (elapsedTime > timeout) {
                throw new TimeOutException();
            }
        }
    }

    public void sendRaw(String s) {
        writer.println(s);
    }

}
