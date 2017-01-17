#include "lib/message.h"
#include "lib/configuration.h"
#include "lib/udptransport.h"
#include "lib/tcptransport.h"
#include "test-client/test-client-proto.pb.h"

#include <thread>
#include <fstream>
#include <sstream>

class Worker : public TransportReceiver
{
public:
    Worker(const string configPath, int id)
        : id(id), n(0), transport(0.0, 0.0, 0, false)
    {
        std::ifstream configStream(configPath, std::ifstream::in);

        fprintf(stderr, "Reading %s %d\n", configPath.c_str());

        if (configStream.fail()) {
            Debug("Unable to read configuration file: %s\n", configPath.c_str());
        }

        config = new transport::Configuration(configStream);

        transport.Register(this, *config, -1);

        transport.Timer(100, [=]() {
            Debug("Scheduling SendMessage");
            this->SendMessage();
        });
    }

    ~Worker() {}

    void Run()
    {
        transport.Run();
    }

    void SendMessage()
    {
        n++;
        if (n > 10) {
            transport.Stop();
            return;
        }

        Debug("Sending Message %d %d", id, n);

        TestMessage msg;
        msg.set_status(n);

        transport.Timer(1000, [=]() {
            if (!transport.SendMessageToReplica(this, 0, msg)) {
                Debug("Unable to send request");
            }

            this->SendMessage();
        });
    }

    void ReceiveMessage(const TransportAddress &remote, const string &type, const string &data)
    {
        Debug("Received reply type: %s", type.c_str());
    }

private:
    int id, n;
    UDPTransport transport;
    //TCPTransport transport;
    transport::Configuration *config;
};

void test_thread(int id)
{
    Worker *w;
    std::stringstream buf;
    buf << "test" << id;

    w = new Worker(buf.str(), id);
    
    w->Run();
}

int main()
{
    std::thread t1(test_thread, 1);
    std::thread t2(test_thread, 2);

    t1.join();
    t2.join();

    return 0;
}
