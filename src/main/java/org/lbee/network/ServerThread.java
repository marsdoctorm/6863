package org.lbee.network;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.net.Socket;

import org.lbee.protocol.Message;

public class ServerThread extends Thread {

    private final Socket socket;
    private final MessageBucket<MessageBox> networkMock;

    public ServerThread(Socket socket, MessageBucket<MessageBox> networkMock) {
        this.socket = socket;
        this.networkMock = networkMock;
    }

    @Override
    public void run() {
        try (socket) {
            InputStream input = socket.getInputStream();
            BufferedReader reader = new BufferedReader(new InputStreamReader(input));
            OutputStream output = socket.getOutputStream();
            PrintWriter writer = new PrintWriter(output, true);

            String text;
            do {
                text = reader.readLine();

                if (text.startsWith("s:")) {
                    String messageData = text.substring(2);
                    Message message = new Message(messageData.split(";"));
                    networkMock.put(message);
                    writer.println("ack");
                    System.out.println("   Message sent: " + message);
                } else if (text.startsWith("r:")) {
                    String dest = text.substring(2);
                    Message message = networkMock.take(dest);
                    writer.println(message != null ? message.toString() : "null");
                }
            } while (!text.equals("bye"));
        } catch (IOException ex) {
            System.out.println("Server exception: " + ex.getMessage());
        }
    }
}
